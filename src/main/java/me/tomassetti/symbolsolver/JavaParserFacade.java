package me.tomassetti.symbolsolver;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.type.*;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.ast.type.ReferenceType;
import me.tomassetti.symbolsolver.model.*;
import me.tomassetti.symbolsolver.model.declarations.*;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.javaparser.declarations.*;
import me.tomassetti.symbolsolver.model.typesolvers.JreTypeSolver;
import me.tomassetti.symbolsolver.model.usages.*;
import me.tomassetti.symbolsolver.model.javaparser.JavaParserFactory;
import me.tomassetti.symbolsolver.model.javaparser.UnsolvedSymbolException;
import me.tomassetti.symbolsolver.model.javaparser.contexts.MethodCallExprContext;

import java.util.*;
import java.util.logging.ConsoleHandler;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.stream.Collector;
import java.util.stream.Collectors;

/**
 * Class to be used by final users to solve symbols for JavaParser ASTs.
 */
public class JavaParserFacade {

    private TypeSolver typeSolver;
    private SymbolSolver symbolSolver;

    private static Logger logger = Logger.getLogger(JavaParserFacade.class.getCanonicalName());
    static {
        logger.setLevel(Level.INFO);
        ConsoleHandler consoleHandler = new ConsoleHandler();
        consoleHandler.setLevel(Level.INFO);
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


    public SymbolReference<? extends ValueDeclaration> solve(NameExpr nameExpr) {
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

    private Map<Node, TypeUsage> cacheWithLambadsSolved = new IdentityHashMap<>();
    private Map<Node, TypeUsage> cacheWithoutLambadsSolved = new IdentityHashMap<>();

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
            Optional<Value> value = new SymbolSolver(typeSolver).solveSymbolAsValue(nameExpr.getName(), nameExpr);
            if (!value.isPresent()){
                throw new UnsolvedSymbolException("FOO Solving "+node, nameExpr.getName());
            } else {
                return value.get().getUsage();
            }
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
                    throw new UnsolvedSymbolException(callExpr.getName());
                }
                logger.finest("getType on lambda expr " + refMethod.getCorrespondingDeclaration().getName());
                //logger.finest("Method param " + refMethod.getCorrespondingDeclaration().getParam(pos));
                if (solveLambdas) {
                    TypeUsage result = refMethod.getCorrespondingDeclaration().getParam(pos).getType(typeSolver);
                    // We need to replace the type variables
                    result = result.solveGenericTypes(JavaParserFactory.getContext(node), typeSolver);
                    return result;
                } else {
                    return refMethod.getCorrespondingDeclaration().getParam(pos).getType(typeSolver);
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
            // We should understand if this is a static access
            try {
                Optional<Value> value = new SymbolSolver(typeSolver).solveSymbolAsValue(fieldAccessExpr.getField(), fieldAccessExpr);
                if (value.isPresent()) {
                    return value.get().getUsage();
                } else {
                    throw new UnsolvedSymbolException(fieldAccessExpr.getField());
                }
            } catch (UnsolvedSymbolException e){
                // Sure, it was not found as value because maybe it is a type and this is a static access
                if (fieldAccessExpr.getScope() instanceof NameExpr){
                    NameExpr staticValue = (NameExpr)fieldAccessExpr.getScope();
                    SymbolReference<TypeDeclaration> typeAccessedStatically = JavaParserFactory.getContext(fieldAccessExpr).solveType(staticValue.toString(), typeSolver);
                    if (!typeAccessedStatically.isSolved()) {
                        throw e;
                    } else {
                        // TODO here maybe we have to substitute type parameters
                        return typeAccessedStatically.getCorrespondingDeclaration().getField(fieldAccessExpr.getField(), typeSolver).getType(typeSolver);
                    }
                } else {
                    throw e;
                }

            }
        } else if (node instanceof ObjectCreationExpr) {
            ObjectCreationExpr objectCreationExpr = (ObjectCreationExpr) node;
            TypeUsage typeUsage = new JavaParserFacade(typeSolver).convertToUsage(objectCreationExpr.getType(), node);
            return typeUsage;
        } else if (node instanceof NullLiteralExpr) {
            return new NullTypeUsage();
        } else if (node instanceof BooleanLiteralExpr) {
            return PrimitiveTypeUsage.BOOLEAN;
        } else if (node instanceof IntegerLiteralExpr) {
            return PrimitiveTypeUsage.INT;
        } else if (node instanceof LongLiteralExpr) {
            return PrimitiveTypeUsage.LONG;
        } else if (node instanceof CharLiteralExpr) {
            return PrimitiveTypeUsage.CHAR;
        } else if (node instanceof StringLiteralExpr) {
            return new TypeUsageOfTypeDeclaration(new JreTypeSolver().solveType("java.lang.String"));
        } else if (node instanceof UnaryExpr) {
            UnaryExpr unaryExpr = (UnaryExpr)node;
            switch (unaryExpr.getOperator()) {
                case negative:
                case positive:
                    return getTypeConcrete(unaryExpr.getExpr(), solveLambdas);
                case not:
                    return PrimitiveTypeUsage.BOOLEAN;
                case posIncrement:
                case preIncrement:
                case preDecrement:
                case posDecrement:
                    return getTypeConcrete(unaryExpr.getExpr(), solveLambdas);
                default:
                    throw new UnsupportedOperationException(unaryExpr.getOperator().name());
            }
        } else if (node instanceof BinaryExpr) {
            BinaryExpr binaryExpr = (BinaryExpr) node;
            switch (binaryExpr.getOperator()) {
                case plus:
                case minus:
                    return getTypeConcrete(binaryExpr.getLeft(), solveLambdas);
                case lessEquals:
                case less:
                case greater:
                case greaterEquals:
                case equals:
                case notEquals:
                case or:
                case and:
                    return PrimitiveTypeUsage.BOOLEAN;
                case binAnd:
                case binOr:
                    return getTypeConcrete(binaryExpr.getLeft(), solveLambdas);
                default:
                    throw new UnsupportedOperationException("FOO " +binaryExpr.getOperator().name());
            }
        } else if (node instanceof VariableDeclarationExpr) {
            VariableDeclarationExpr expr = (VariableDeclarationExpr)node;
            return convertToUsage(expr.getType(), JavaParserFactory.getContext(node));
        } else if (node instanceof InstanceOfExpr) {
            return PrimitiveTypeUsage.BOOLEAN;
        } else if (node instanceof EnclosedExpr) {
            EnclosedExpr enclosedExpr = (EnclosedExpr)node;
            return getTypeConcrete(enclosedExpr.getInner(), solveLambdas);
        } else if (node instanceof CastExpr) {
            CastExpr enclosedExpr = (CastExpr)node;
            return convertToUsage(enclosedExpr.getType(), JavaParserFactory.getContext(node));
        } else if (node instanceof AssignExpr) {
            AssignExpr assignExpr = (AssignExpr) node;
            return getTypeConcrete(assignExpr.getTarget(), solveLambdas);
        } else if (node instanceof ThisExpr) {
            return new TypeUsageOfTypeDeclaration(getTypeDeclaration(findContainingTypeDecl(node)));
        } else if (node instanceof ConditionalExpr) {
            ConditionalExpr conditionalExpr = (ConditionalExpr)node;
            return getTypeConcrete(conditionalExpr.getThenExpr(), solveLambdas);
        } else if (node instanceof ArrayCreationExpr) {
            ArrayCreationExpr arrayCreationExpr = (ArrayCreationExpr)node;
            return convertToUsage(arrayCreationExpr.getType(), JavaParserFactory.getContext(node));
        } else {
            throw new UnsupportedOperationException(node.getClass().getCanonicalName());
        }
    }

    private ClassOrInterfaceDeclaration findContainingTypeDecl(Node node){
        if (node instanceof ClassOrInterfaceDeclaration) {
            return (ClassOrInterfaceDeclaration)node;
        } else if (node.getParentNode() == null) {
            throw new IllegalArgumentException();
        } else {
            return findContainingTypeDecl(node.getParentNode());
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
            ClassOrInterfaceType classOrInterfaceType = (ClassOrInterfaceType) type;
            SymbolReference<TypeDeclaration> ref = context.solveType(classOrInterfaceType.getName(), typeSolver);
            if (!ref.isSolved()) {
                throw new UnsolvedSymbolException(classOrInterfaceType.getName());
            }
            TypeDeclaration typeDeclaration = ref.getCorrespondingDeclaration();
            List<TypeUsage> typeParameters = Collections.emptyList();
            if (classOrInterfaceType.getTypeArgs() != null) {
                typeParameters = classOrInterfaceType.getTypeArgs().stream().map((pt) -> convertToUsage(pt, context)).collect(Collectors.toList());
            }
            if (typeDeclaration.isTypeVariable()) {
                if (typeDeclaration instanceof TypeParameter) {
                    return new TypeUsageOfTypeParameter((TypeParameter)typeDeclaration);
                } else {
                    JavaParserTypeVariableDeclaration javaParserTypeVariableDeclaration = (JavaParserTypeVariableDeclaration) typeDeclaration;
                    return new TypeUsageOfTypeParameter(javaParserTypeVariableDeclaration.asTypeParameter());
                }
            } else {
                return new TypeUsageOfTypeDeclaration(typeDeclaration, typeParameters);
            }
        } else if (type instanceof PrimitiveType) {
            return PrimitiveTypeUsage.byName(((PrimitiveType) type).getType().name());
        } else if (type instanceof WildcardType) {
            return new WildcardUsage((WildcardType)type);
        } else if (type instanceof VoidType) {
            return new VoidTypeUsage();
        } else {
            throw new UnsupportedOperationException("FOO " +type.getClass().getCanonicalName());
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

    public TypeUsage convert(Type type, Node node) {
        return convert(type, JavaParserFactory.getContext(node));
    }

    public TypeUsage convert(Type type, Context context) {
        return convertToUsage(type, context);
    }

    public MethodUsage solveMethodAsUsage(MethodCallExpr call) {
        List<TypeUsage> params = new ArrayList<>();
        if (call.getArgs() != null) {
            for (Expression param : call.getArgs()) {
                params.add(getType(param, false));
            }
        }
        Context context = JavaParserFactory.getContext(call);
        Optional<MethodUsage> methodUsage = context.solveMethodAsUsage(call.getName(), params, typeSolver);
        if (!methodUsage.isPresent()) {
            throw new RuntimeException("Method" +
                    " '"+call.getName()+"' cannot be resolved in context " + call+ " (line: "+call.getBeginLine()+") "+context);
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

    public TypeDeclaration getTypeDeclaration(ClassOrInterfaceDeclaration classOrInterfaceDeclaration){
        if (classOrInterfaceDeclaration.isInterface()) {
            return new JavaParserInterfaceDeclaration(classOrInterfaceDeclaration);
        } else {
            return new JavaParserClassDeclaration(classOrInterfaceDeclaration);
        }
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

    public TypeUsage convertToUsage(TypeDeclaration typeDeclaration) {
        if (typeDeclaration.isTypeVariable()) {
            if (typeDeclaration instanceof JavaParserTypeParameter) {
                return new TypeUsageOfTypeParameter((JavaParserTypeParameter)typeDeclaration);
            } else {
                JavaParserTypeVariableDeclaration javaParserTypeVariableDeclaration = (JavaParserTypeVariableDeclaration) typeDeclaration;
                return new TypeUsageOfTypeParameter(javaParserTypeVariableDeclaration.asTypeParameter());
            }
        } else {
            return new TypeUsageOfTypeDeclaration(typeDeclaration);
        }
    }

    public TypeDeclaration getTypeDeclaration(com.github.javaparser.ast.body.TypeDeclaration typeDeclaration) {
        if (typeDeclaration instanceof ClassOrInterfaceDeclaration) {
            return getTypeDeclaration((ClassOrInterfaceDeclaration)typeDeclaration);
        } else if (typeDeclaration instanceof EnumDeclaration){
            return new JavaParserEnumDeclaration((EnumDeclaration)typeDeclaration);
        } else {
            throw new UnsupportedOperationException(typeDeclaration.getClass().getCanonicalName());
        }
    }
}
