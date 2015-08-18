package me.tomassetti.symbolsolver;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.type.*;
import jdk.nashorn.internal.ir.Symbol;
import me.tomassetti.symbolsolver.model.*;
import me.tomassetti.symbolsolver.model.declarations.*;
import me.tomassetti.symbolsolver.model.javaparser.declarations.JavaParserClassDeclaration;
import me.tomassetti.symbolsolver.model.usages.MethodUsage;
import me.tomassetti.symbolsolver.model.usages.NullTypeUsage;
import me.tomassetti.symbolsolver.model.usages.TypeUsageOfTypeDeclaration;
import me.tomassetti.symbolsolver.model.javaparser.JavaParserFactory;
import me.tomassetti.symbolsolver.model.javaparser.UnsolvedSymbolException;
import me.tomassetti.symbolsolver.model.javaparser.contexts.MethodCallExprContext;
import me.tomassetti.symbolsolver.model.javaparser.declarations.JavaParserSymbolDeclaration;
import me.tomassetti.symbolsolver.model.usages.TypeUsage;

import java.lang.reflect.Method;
import java.util.*;
import java.util.logging.ConsoleHandler;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.stream.Collectors;

/**
 * Class to be used by final users to solve symbols for JavaParser ASTs.
 */
public class JavaParserFacade {

    private TypeSolver typeSolver;
    private SymbolSolver symbolSolver;

    private static Logger logger = Logger.getLogger(JavaParserFacade.class.getCanonicalName());
    static {
        logger.setLevel(Level.FINEST);
        ConsoleHandler consoleHandler = new ConsoleHandler();
        consoleHandler.setLevel(Level.FINER);
        logger.addHandler(consoleHandler);
    }

    private JavaParserFacade(TypeSolver typeSolver) {
        this.typeSolver = typeSolver;
        this.symbolSolver = new SymbolSolver(typeSolver);
    }

    public static JavaParserFacade get(TypeSolver typeSolver){
        if (!instances.containsKey(typeSolver)){
            instances.put(typeSolver, new JavaParserFacade(typeSolver));
        }
        return instances.get(typeSolver);
    }


    public SymbolReference solve(NameExpr nameExpr) {
        return symbolSolver.solveSymbol(nameExpr.getName(), nameExpr);
    }

    public SymbolReference solve(Expression expr) {
        if (expr instanceof NameExpr) {
            return solve((NameExpr)expr);
        } else {
            throw new IllegalArgumentException(expr.getClass().getCanonicalName());
        }
    }

    /**
     * Given a method call find out to which method declaration it corresponds.
     */
    public SymbolReference<MethodDeclaration> solve(MethodCallExpr methodCallExpr) {
        List<TypeUsage> params = new LinkedList<>();
        List<LambdaTypeUsagePlaceholder> placeholders = new LinkedList<>();
        int i = 0;
        for (Expression expression : methodCallExpr.getArgs()) {
            if (expression instanceof LambdaExpr) {
                LambdaTypeUsagePlaceholder placeholder = new LambdaTypeUsagePlaceholder(i);
                params.add(placeholder);
                placeholders.add(placeholder);
            } else {
                params.add(new JavaParserFacade(typeSolver).getType(expression));
            }
            i++;
        }
        SymbolReference<MethodDeclaration> res = JavaParserFactory.getContext(methodCallExpr).solveMethod(methodCallExpr.getName(), params, typeSolver);
        for (LambdaTypeUsagePlaceholder placeholder : placeholders) {
            placeholder.setMethod(res);
        }
        return res;
    }

    public TypeUsage getType(Node node) {
        return getType(node, true);
    }

    private Map<Node, TypeUsage> cacheWithLambadsSolved = new WeakHashMap<>();
    private Map<Node, TypeUsage> cacheWithoutLambadsSolved = new WeakHashMap<>();

    private static Map<TypeSolver, JavaParserFacade> instances = new HashMap<>();

    public TypeUsage getType(Node node, boolean solveLambdas) {
        if (solveLambdas){
            if (!cacheWithLambadsSolved.containsKey(node)){
                TypeUsage res = getTypeConcrete(node, solveLambdas);
                cacheWithLambadsSolved.put(node, res);
                logger.finer("getType on " + node + " -> " + res);
            }
            return cacheWithLambadsSolved.get(node);
        } else {
            if (!cacheWithoutLambadsSolved.containsKey(node)){
                TypeUsage res = getTypeConcrete(node, solveLambdas);
                cacheWithoutLambadsSolved.put(node, res);
                logger.finer("getType on " + node + " (no solveLambdas) -> " + res);
            }
            return cacheWithoutLambadsSolved.get(node);
        }
    }

    /**
     * Should return more like a TypeApplication: a TypeDeclaration and possible parameters or array modifiers.
     * @return
     */
    private TypeUsage getTypeConcrete(Node node, boolean solveLambdas) {
        if (node == null) throw new IllegalArgumentException();
        if (node instanceof NameExpr) {
            NameExpr nameExpr = (NameExpr) node;
            logger.finest("getType on name expr " + node);
            return new SymbolSolver(typeSolver).solveSymbolAsValue(nameExpr.getName(), nameExpr).get().getUsage();
        } else if (node instanceof MethodCallExpr) {
            logger.finest("getType on method call " + node);
            // first solve the method
            MethodUsage ref = new JavaParserFacade(typeSolver).solveMethodAsUsage((MethodCallExpr) node);
            logger.finest("getType on method call " + node + " resolved to " + ref);
            logger.finest("getType on method call " + node + " return type is " + ref.returnType());
            return ref.returnType();
            // the type is the return type of the method
        } else if (node instanceof LambdaExpr) {
            if (node.getParentNode() instanceof MethodCallExpr) {
                MethodCallExpr callExpr = (MethodCallExpr) node.getParentNode();
                int pos = JavaParserSymbolDeclaration.getParamPos(node);
                SymbolReference<MethodDeclaration> refMethod = new JavaParserFacade(typeSolver).solve(callExpr);
                if (!refMethod.isSolved()) {
                    throw new UnsolvedSymbolException(null, callExpr.getName());
                }
                logger.finest("getType on lambda expr " + refMethod.getCorrespondingDeclaration().getName());
                //logger.finest("Method param " + refMethod.getCorrespondingDeclaration().getParam(pos));
                if (solveLambdas) {
                    TypeUsage result = refMethod.getCorrespondingDeclaration().getParam(pos).getType(typeSolver).getUsage(node);
                    // We need to replace the type variables
                    result = result.solveGenericTypes(JavaParserFactory.getContext(node), typeSolver);
                    return result;
                } else {
                    return new TypeUsageOfTypeDeclaration(refMethod.getCorrespondingDeclaration().getParam(pos).getType(typeSolver));
                }
                //System.out.println("LAMBDA " + node.getParentNode());
                //System.out.println("LAMBDA CLASS " + node.getParentNode().getClass().getCanonicalName());
                //TypeUsage typeOfMethod = new JavaParserFacade(typeSolver).getType(node.getParentNode());
                //throw new UnsupportedOperationException("The type of a lambda expr depends on the position and its return value");
            } else {
                throw new UnsupportedOperationException("The type of a lambda expr depends on the position and its return value");
            }
        } else if (node instanceof VariableDeclarator) {
            if (node.getParentNode() instanceof FieldDeclaration) {
                FieldDeclaration parent = (FieldDeclaration) node.getParentNode();
                return new JavaParserFacade(typeSolver).convertToUsage(parent.getType(), parent);
            } else if (node.getParentNode() instanceof VariableDeclarationExpr) {
                VariableDeclarationExpr parent = (VariableDeclarationExpr) node.getParentNode();
                return new JavaParserFacade(typeSolver).convertToUsage(parent.getType(), parent);
            } else {
                throw new UnsupportedOperationException(node.getParentNode().getClass().getCanonicalName());
            }
        } else if (node instanceof Parameter) {
            Parameter parameter = (Parameter)node;
            if (parameter.getType() instanceof UnknownType){
                throw new IllegalStateException("Parameter has unknown type: " + parameter);
            }
            return new JavaParserFacade(typeSolver).convertToUsage(parameter.getType(), parameter);
        } else if (node instanceof FieldAccessExpr) {
            FieldAccessExpr fieldAccessExpr = (FieldAccessExpr) node;
            Optional<Value> value = new SymbolSolver(typeSolver).solveSymbolAsValue(fieldAccessExpr.getField(), fieldAccessExpr);
            if (value.isPresent()) {
                return value.get().getUsage();
            } else {
                throw new UnsolvedSymbolException(null, fieldAccessExpr.getField());
            }
        } else if (node instanceof ObjectCreationExpr) {
            ObjectCreationExpr objectCreationExpr = (ObjectCreationExpr) node;
            TypeUsage typeUsage = new JavaParserFacade(typeSolver).convertToUsage(objectCreationExpr.getType(), node);
            return typeUsage;
        } else if (node instanceof NullLiteralExpr) {
            return new NullTypeUsage();
        } else {
            throw new UnsupportedOperationException(node.getClass().getCanonicalName());
        }
    }

    public TypeUsage convertToUsage(Type type, Node context) {
        if (type instanceof UnknownType){
            throw new IllegalArgumentException("Unknown type");
        }
        return convertToUsage(type, JavaParserFactory.getContext(context));
    }

    public TypeUsage convertToUsage(Type type, Context context) {
        if (type instanceof ReferenceType) {
            ReferenceType referenceType = (ReferenceType) type;
            // TODO consider array modifiers
            return convertToUsage(referenceType.getType(), context);
        } else if (type instanceof ClassOrInterfaceType) {
            ClassOrInterfaceType classOrInterfaceType = (ClassOrInterfaceType)type;
            SymbolReference<TypeDeclaration> ref = context.solveType(classOrInterfaceType.getName(), typeSolver);
            if (!ref.isSolved()) {
                throw new UnsolvedSymbolException(null, classOrInterfaceType.getName());
            }
            TypeDeclaration typeDeclaration = ref.getCorrespondingDeclaration();
            List<TypeUsage> typeParameters = Collections.emptyList();
            if (classOrInterfaceType.getTypeArgs() != null) {
                typeParameters = classOrInterfaceType.getTypeArgs().stream().map((pt)->convertToUsage(pt, context)).collect(Collectors.toList());
            }
            return new TypeUsageOfTypeDeclaration(typeDeclaration, typeParameters);
        } else {
            throw new UnsupportedOperationException(type.getClass().getCanonicalName());
        }
    }

    private SymbolReference<MethodDeclaration> solveMethod(MethodCallExpr methodCallExpr) {
        List<TypeUsage> params = new ArrayList<>();
        if (methodCallExpr.getArgs() != null) {
            for (Expression param : methodCallExpr.getArgs()) {
                params.add(getType(param));
            }
        }
        return new MethodCallExprContext(methodCallExpr).solveMethod(methodCallExpr.getName(), params, typeSolver);
    }

    public TypeDeclaration convert(Type type, Node node) {
        return convert(type, JavaParserFactory.getContext(node));
    }

    public TypeDeclaration convert(Type type, Context context) {
        if (type instanceof ReferenceType) {
            ReferenceType referenceType = (ReferenceType) type;
            // TODO consider array modifiers
            return convert(referenceType.getType(), context);
        } else if (type instanceof ClassOrInterfaceType) {
            ClassOrInterfaceType classOrInterfaceType = (ClassOrInterfaceType) type;
            SymbolReference<TypeDeclaration> ref = context.solveType(classOrInterfaceType.getName(), typeSolver);
            if (!ref.isSolved()) {
                throw new UnsolvedSymbolException(null, classOrInterfaceType.getName());
            }
            return ref.getCorrespondingDeclaration();
        } else if (type instanceof VoidType) {
            return new VoidTypeDeclaration();
        } else if (type instanceof PrimitiveType) {
            return new PrimitiveTypeDeclaration((PrimitiveType)type);
        } else {
            throw new UnsupportedOperationException(type.getClass().getCanonicalName());
        }
    }

    public MethodUsage solveMethodAsUsage(MethodCallExpr call) {
        List<TypeUsage> params = new ArrayList<>();
        if (call.getArgs() != null) {
            for (Expression param : call.getArgs()) {
                params.add(getType(param, false));
            }
        }
        /*TypeUsage typeOfScope = getType(call.getScope());
        logger.finest("facade solveMethodAsUsage, params " + params);
        logger.finest("facade solveMethodAsUsage, scope " + typeOfScope);

        // TODO take params from scope and substitute them in ref

        Optional<MethodUsage> ref = new MethodCallExprContext(call).solveMethodAsUsage(call.getName(), params, typeSolver);

        if (!ref.isPresent()){
            throw new UnsolvedSymbolException(null, call.getName());
        } else {
            logger.finest("facade solveMethodAsUsage, ref " + ref.get());
            MethodUsage methodUsage = ref.get();
            methodUsage = replaceParams(methodUsage, typeOfScope);
            TypeUsage returnType = replaceParams(methodUsage.returnType(), typeOfScope);
            methodUsage = methodUsage.replaceReturnType(returnType);
            return methodUsage;
        }*/
        Context context = JavaParserFactory.getContext(call);
        Optional<MethodUsage> methodUsage = context.solveMethodAsUsage(call.getName(), params, typeSolver);
        if (!methodUsage.isPresent()) {
            throw new RuntimeException("Method cannot be resolved " + call.getName());
        }
        return methodUsage.get();
    }

    private MethodUsage replaceParams(MethodUsage methodUsage, TypeUsage typeOfScope) {
        logger.finest("ReplaceParams " + methodUsage);
        logger.finest("ReplaceParams N params " + methodUsage.getParamTypes().size());
        for (int i=0;i<methodUsage.getParamTypes().size();i++) {
            TypeUsage typeUsage = methodUsage.getParamTypes().get(i);
            TypeUsage replaced = replaceParams(typeUsage, typeOfScope);
            logger.finest("ReplaceParams param type " + typeUsage);
            if (replaced != typeUsage) {
                logger.finest("ReplaceParams param -> " + replaced);
                methodUsage = methodUsage.replaceParamType(i, replaced);
            }
        }
        logger.finest("Final method usage "+methodUsage);
        return methodUsage;
    }

    public static TypeUsage replaceParams(TypeUsage typeToReplace, TypeUsage typeOfScope) {
        if (typeToReplace.isTypeVariable()) {
            Optional<TypeUsage> replacement = typeOfScope.parameterByName(typeToReplace.getTypeName());
            if (replacement.isPresent()) {
                return replacement.get();
            } else {
                return typeToReplace;
            }
        } else {
            for (int i=0;i<typeToReplace.parameters().size();i++){
                TypeUsage typeUsage = typeToReplace.parameters().get(i);
                TypeUsage replaced = replaceParams(typeUsage, typeOfScope);
                if (replaced != typeUsage) {
                    typeToReplace = typeToReplace.replaceParam(i, replaced);
                }
            }
            return typeToReplace;
        }
    }

    public MethodUsage convertToUsage(MethodDeclaration methodDeclaration, Context context) {
        return new MethodUsage(methodDeclaration, typeSolver);
    }

    /**
     * "this" inserted in the given point, which type would have?
     */
    public TypeUsage getTypeOfThisIn(Node node) {
        // TODO consider static methods
        if (node instanceof ClassOrInterfaceDeclaration) {
            JavaParserClassDeclaration classDeclaration = new JavaParserClassDeclaration((ClassOrInterfaceDeclaration)node);
            return new TypeUsageOfTypeDeclaration(classDeclaration);
        } else {
            return getTypeOfThisIn(node.getParentNode());
        }
    }
}
