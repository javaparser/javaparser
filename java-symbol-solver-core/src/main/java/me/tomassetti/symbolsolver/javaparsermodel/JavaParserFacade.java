package me.tomassetti.symbolsolver.javaparsermodel;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.UnknownType;
import com.github.javaparser.ast.type.WildcardType;
import javaslang.Tuple2;
import me.tomassetti.symbolsolver.javaparsermodel.declarations.*;
import me.tomassetti.symbolsolver.logic.FunctionalInterfaceLogic;
import me.tomassetti.symbolsolver.logic.GenericTypeInferenceLogic;
import me.tomassetti.symbolsolver.model.declarations.*;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.usages.MethodUsage;
import me.tomassetti.symbolsolver.core.resolution.Context;
import me.tomassetti.symbolsolver.model.resolution.SymbolReference;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.usages.typesystem.*;
import me.tomassetti.symbolsolver.model.usages.typesystem.TypeParameter;
import me.tomassetti.symbolsolver.reflectionmodel.ReflectionClassDeclaration;
import me.tomassetti.symbolsolver.resolution.SymbolSolver;
import me.tomassetti.symbolsolver.resolution.typesolvers.JreTypeSolver;

import java.util.*;
import java.util.logging.ConsoleHandler;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.stream.Collectors;

/**
 * Class to be used by final users to solve symbols for JavaParser ASTs.
 */
public class JavaParserFacade {

    private static Logger logger = Logger.getLogger(JavaParserFacade.class.getCanonicalName());
    static {
        logger.setLevel(Level.INFO);
        ConsoleHandler consoleHandler = new ConsoleHandler();
        consoleHandler.setLevel(Level.INFO);
        logger.addHandler(consoleHandler);
    }
    private static Map<TypeSolver, JavaParserFacade> instances = new HashMap<>();
    private TypeSolver typeSolver;
    private SymbolSolver symbolSolver;
    private Map<Node, Type> cacheWithLambdasSolved = new IdentityHashMap<>();
    private Map<Node, Type> cacheWithoutLambadsSolved = new IdentityHashMap<>();

    private JavaParserFacade(TypeSolver typeSolver) {
        this.typeSolver = typeSolver.getRoot();
        this.symbolSolver = new SymbolSolver(typeSolver);
    }

    public static JavaParserFacade get(TypeSolver typeSolver) {
        if (!instances.containsKey(typeSolver)) {
            instances.put(typeSolver, new JavaParserFacade(typeSolver));
        }
        return instances.get(typeSolver);
    }

    /**
     * This method is used to clear internal caches for the sake of releasing memory.
     */
    public static void clearInstances() {
	    instances.clear();
    }

    private static Type solveGenericTypes(Type type, Context context, TypeSolver typeSolver) {
        if (type.isTypeVariable()) {
            Optional<Type> solved = context.solveGenericType(type.describe(), typeSolver);
            if (solved.isPresent()) {
                return solved.get();
            } else {
                return type;
            }
        } else if (type.isWildcard()) {
            if (type.asWildcard().isExtends() || type.asWildcard().isSuper()) {
                Wildcard wildcardUsage = type.asWildcard();
                Type boundResolved = solveGenericTypes(wildcardUsage.getBoundedType(), context, typeSolver);
                if (wildcardUsage.isExtends()) {
                    return Wildcard.extendsBound(boundResolved);
                } else {
                    return Wildcard.superBound(boundResolved);
                }
            } else {
                return type;
            }
        } else {
            Type result = type;
            int i = 0;
            if (result.isReferenceType()) {
                for (Type tp : type.asReferenceType().typeParametersValues()) {
                    result = result.asReferenceType().replaceParam(i, solveGenericTypes(tp, context, typeSolver));
                    i++;
                }
            }
            return result;
        }
    }

    public SymbolReference<? extends ValueDeclaration> solve(NameExpr nameExpr) {
        return symbolSolver.solveSymbol(nameExpr.getName(), nameExpr);
    }

    public SymbolReference solve(Expression expr) {
        if (expr instanceof NameExpr) {
            return solve((NameExpr) expr);
        } else {
            throw new IllegalArgumentException(expr.getClass().getCanonicalName());
        }
    }

    public SymbolReference<MethodDeclaration> solve(MethodCallExpr methodCallExpr) {
        return solve(methodCallExpr, true);
    }

    /**
     * Given a method call find out to which method declaration it corresponds.
     */
    public SymbolReference<MethodDeclaration> solve(MethodCallExpr methodCallExpr, boolean solveLambdas) {
        List<Type> params = new LinkedList<>();
        List<LambdaArgumentTypePlaceholder> placeholders = new LinkedList<>();
        int i = 0;
        for (Expression parameterValue : methodCallExpr.getArgs()) {
            if (parameterValue instanceof LambdaExpr || parameterValue instanceof MethodReferenceExpr) {
                LambdaArgumentTypePlaceholder placeholder = new LambdaArgumentTypePlaceholder(i);
                params.add(placeholder);
                placeholders.add(placeholder);
            } else {
                try {
                    params.add(JavaParserFacade.get(typeSolver).getType(parameterValue, solveLambdas));
                } catch (Exception e){
                    throw new RuntimeException(String.format("Unable to calculate the type of a parameter of a method call. Method call: %s, Parameter: %s",
                            methodCallExpr, parameterValue), e);
                }
            }
            i++;
        }
        SymbolReference<MethodDeclaration> res = JavaParserFactory.getContext(methodCallExpr, typeSolver).solveMethod(methodCallExpr.getName(), params, typeSolver);
        for (LambdaArgumentTypePlaceholder placeholder : placeholders) {
            placeholder.setMethod(res);
        }
        return res;
    }

    public Type getType(Node node) {
        return getType(node, true);
    }

    public Type getType(Node node, boolean solveLambdas) {
        if (solveLambdas) {
            if (!cacheWithLambdasSolved.containsKey(node)) {
                Type res = getTypeConcrete(node, solveLambdas);

                cacheWithLambdasSolved.put(node, res);

                boolean secondPassNecessary = false;
                if (node instanceof MethodCallExpr) {
                    MethodCallExpr methodCallExpr = (MethodCallExpr)node;
                    for (Node arg : methodCallExpr.getArgs()) {
                        if (!cacheWithLambdasSolved.containsKey(arg)) {
                            getType(arg, true);
                            secondPassNecessary = true;
                        }
                    }
                }
                if (secondPassNecessary) {
                    cacheWithLambdasSolved.remove(node);
                    cacheWithLambdasSolved.put(node, getType(node, true));
                }
                logger.finer("getType on " + node + " -> " + res);
            }
            return cacheWithLambdasSolved.get(node);
        } else {
            Optional<Type> res = find(cacheWithLambdasSolved, node);
            if (res.isPresent()) {
                return res.get();
            }
            res = find(cacheWithoutLambadsSolved, node);
            if (!res.isPresent()) {
                Type resType = getTypeConcrete(node, solveLambdas);
                cacheWithoutLambadsSolved.put(node, resType);
                logger.finer("getType on " + node + " (no solveLambdas) -> " + res);
                return resType;
            }
            return res.get();
        }
    }

    private Optional<Type> find(Map<Node, Type> map, Node node) {
        if (map.containsKey(node)) {
            return Optional.of(map.get(node));
        }
        if (node instanceof LambdaExpr) {
            return find(map, (LambdaExpr)node);
        } else {
            return Optional.empty();
        }
    }

    /**
     * For some reasons LambdaExprs are duplicate and the equals method is not implemented correctly.
     * @param map
     * @return
     */
    private Optional<Type> find(Map<Node, Type> map, LambdaExpr lambdaExpr) {
        for (Node key : map.keySet()) {
            if (key instanceof LambdaExpr) {
                LambdaExpr keyLambdaExpr = (LambdaExpr)key;
                if (keyLambdaExpr.toString().equals(lambdaExpr.toString()) && keyLambdaExpr.getParentNode() == lambdaExpr.getParentNode()) {
                    return Optional.of(map.get(keyLambdaExpr));
                }
            }
        }
        return Optional.empty();
    }

    private MethodUsage toMethodUsage(MethodReferenceExpr methodReferenceExpr) {
        if (!(methodReferenceExpr.getScope() instanceof TypeExpr)) {
            throw new UnsupportedOperationException();
        }
        TypeExpr typeExpr = (TypeExpr)methodReferenceExpr.getScope();
        if (!(typeExpr.getType() instanceof com.github.javaparser.ast.type.ReferenceType)) {
            throw new UnsupportedOperationException(typeExpr.getType().getClass().getCanonicalName());
        }
        com.github.javaparser.ast.type.ReferenceType referenceType = (com.github.javaparser.ast.type.ReferenceType)typeExpr.getType();
        if (!(referenceType.getType() instanceof ClassOrInterfaceType)) {
            throw new UnsupportedOperationException(referenceType.getType().getClass().getCanonicalName());
        }
        ClassOrInterfaceType classOrInterfaceType = (ClassOrInterfaceType)referenceType.getType();
        SymbolReference<TypeDeclaration> typeDeclarationSymbolReference = JavaParserFactory.getContext(classOrInterfaceType, typeSolver).solveType(classOrInterfaceType.getName(), typeSolver);
        if (!typeDeclarationSymbolReference.isSolved()) {
            throw new UnsupportedOperationException();
        }
        List<MethodUsage> methodUsages = typeDeclarationSymbolReference.getCorrespondingDeclaration().getAllMethods().stream().filter(it -> it.getName().equals(methodReferenceExpr.getIdentifier())).collect(Collectors.toList());
        switch (methodUsages.size()) {
            case 0:
                throw new UnsupportedOperationException();
            case 1:
                return methodUsages.get(0);
            default:
                throw new UnsupportedOperationException();
        }
    }

    /**
     * Should return more like a TypeApplication: a TypeDeclaration and possible typeParametersValues or array modifiers.
     *
     * @return
     */
    private Type getTypeConcrete(Node node, boolean solveLambdas) {
        if (node == null) throw new IllegalArgumentException();
        if (node instanceof NameExpr) {
            NameExpr nameExpr = (NameExpr) node;
            logger.finest("getType on name expr " + node);
            Optional<me.tomassetti.symbolsolver.model.resolution.Value> value = new SymbolSolver(typeSolver).solveSymbolAsValue(nameExpr.getName(), nameExpr);
            if (!value.isPresent()) {
                throw new UnsolvedSymbolException("Solving " + node, nameExpr.getName());
            } else {
                return value.get().getUsage();
            }
        } else if (node instanceof MethodCallExpr) {
            logger.finest("getType on method call " + node);
            // first solve the method
            MethodUsage ref = solveMethodAsUsage((MethodCallExpr) node);
            logger.finest("getType on method call " + node + " resolved to " + ref);
            logger.finest("getType on method call " + node + " return type is " + ref.returnType());
            return ref.returnType();
            // the type is the return type of the method
        } else if (node instanceof LambdaExpr) {
            if (node.getParentNode() instanceof MethodCallExpr) {
                MethodCallExpr callExpr = (MethodCallExpr) node.getParentNode();
                int pos = JavaParserSymbolDeclaration.getParamPos(node);
                SymbolReference<MethodDeclaration> refMethod = JavaParserFacade.get(typeSolver).solve(callExpr);
                if (!refMethod.isSolved()) {
                    throw new UnsolvedSymbolException(node.getParentNode().toString(), callExpr.getName());
                }
                logger.finest("getType on lambda expr " + refMethod.getCorrespondingDeclaration().getName());
                //logger.finest("Method param " + refMethod.getCorrespondingDeclaration().getParam(pos));
                if (solveLambdas) {
                    Type result = refMethod.getCorrespondingDeclaration().getParam(pos).getType();
                    // We need to replace the type variables
                    Context ctx = JavaParserFactory.getContext(node, typeSolver);
                    result = solveGenericTypes(result, ctx, typeSolver);

                    //We should find out which is the functional method (e.g., apply) and replace the params of the
                    //solveLambdas with it, to derive so the values. We should also consider the value returned by the
                    //lambdas
                    Optional<MethodUsage> functionalMethod = FunctionalInterfaceLogic.getFunctionalMethod(result);
                    if (functionalMethod.isPresent()) {
                        LambdaExpr lambdaExpr = (LambdaExpr) node;

                        List<Tuple2<Type, Type>> formalActualTypePairs = new ArrayList<>();
                        if (lambdaExpr.getBody() instanceof ExpressionStmt) {
                            ExpressionStmt expressionStmt = (ExpressionStmt) lambdaExpr.getBody();
                            Type actualType = getType(expressionStmt.getExpression());
                            Type formalType = functionalMethod.get().returnType();
                            formalActualTypePairs.add(new Tuple2<>(formalType, actualType));
                            Map<String, Type> inferredTypes = GenericTypeInferenceLogic.inferGenericTypes(formalActualTypePairs);
                            for (String typeName : inferredTypes.keySet()) {
                                result = result.replaceParam(typeName, inferredTypes.get(typeName));
                            }
                        } else {
                            throw new UnsupportedOperationException();
                        }
                    }

                    return result;
                } else {
                    return refMethod.getCorrespondingDeclaration().getParam(pos).getType();
                }
            } else {
                throw new UnsupportedOperationException("The type of a lambda expr depends on the position and its return value");
            }
        } else if (node instanceof MethodReferenceExpr) {
            if (node.getParentNode() instanceof MethodCallExpr) {
                MethodCallExpr callExpr = (MethodCallExpr) node.getParentNode();
                int pos = JavaParserSymbolDeclaration.getParamPos(node);
                SymbolReference<MethodDeclaration> refMethod = JavaParserFacade.get(typeSolver).solve(callExpr, false);
                if (!refMethod.isSolved()) {
                    throw new UnsolvedSymbolException(node.getParentNode().toString(), callExpr.getName());
                }
                logger.finest("getType on method reference expr " + refMethod.getCorrespondingDeclaration().getName());
                //logger.finest("Method param " + refMethod.getCorrespondingDeclaration().getParam(pos));
                if (solveLambdas) {
                    Type result = refMethod.getCorrespondingDeclaration().getParam(pos).getType();
                    // We need to replace the type variables
                    Context ctx = JavaParserFactory.getContext(node, typeSolver);
                    result = solveGenericTypes(result, ctx, typeSolver);

                    //We should find out which is the functional method (e.g., apply) and replace the params of the
                    //solveLambdas with it, to derive so the values. We should also consider the value returned by the
                    //lambdas
                    Optional<MethodUsage> functionalMethod = FunctionalInterfaceLogic.getFunctionalMethod(result);
                    if (functionalMethod.isPresent()) {
                        if (node instanceof MethodReferenceExpr) {
                            MethodReferenceExpr methodReferenceExpr = (MethodReferenceExpr) node;

                            List<Tuple2<Type, Type>> formalActualTypePairs = new ArrayList<>();
                            Type actualType = toMethodUsage(methodReferenceExpr).returnType();
                            Type formalType = functionalMethod.get().returnType();
                            formalActualTypePairs.add(new Tuple2<>(formalType, actualType));
                            Map<String, Type> inferredTypes = GenericTypeInferenceLogic.inferGenericTypes(formalActualTypePairs);
                            for (String typeName : inferredTypes.keySet()) {
                                result = result.replaceParam(typeName, inferredTypes.get(typeName));
                            }

                        } else {
                            LambdaExpr lambdaExpr = (LambdaExpr) node;

                            List<Tuple2<Type, Type>> formalActualTypePairs = new ArrayList<>();
                            if (lambdaExpr.getBody() instanceof ExpressionStmt) {
                                ExpressionStmt expressionStmt = (ExpressionStmt) lambdaExpr.getBody();
                                Type actualType = getType(expressionStmt.getExpression());
                                Type formalType = functionalMethod.get().returnType();
                                formalActualTypePairs.add(new Tuple2<>(formalType, actualType));
                                Map<String, Type> inferredTypes = GenericTypeInferenceLogic.inferGenericTypes(formalActualTypePairs);
                                for (String typeName : inferredTypes.keySet()) {
                                    result = result.replaceParam(typeName, inferredTypes.get(typeName));
                                }
                            } else {
                                throw new UnsupportedOperationException();
                            }
                        }
                    }

                    return result;
                } else {
                    return refMethod.getCorrespondingDeclaration().getParam(pos).getType();
                }
            } else {
                throw new UnsupportedOperationException("The type of a method reference expr depends on the position and its return value");
            }
        } else if (node instanceof VariableDeclarator) {
            if (node.getParentNode() instanceof FieldDeclaration) {
                FieldDeclaration parent = (FieldDeclaration) node.getParentNode();
                return JavaParserFacade.get(typeSolver).convertToUsage(parent.getType(), parent);
            } else if (node.getParentNode() instanceof VariableDeclarationExpr) {
                VariableDeclarationExpr parent = (VariableDeclarationExpr) node.getParentNode();
                return JavaParserFacade.get(typeSolver).convertToUsage(parent.getType(), parent);
            } else {
                throw new UnsupportedOperationException(node.getParentNode().getClass().getCanonicalName());
            }
        } else if (node instanceof Parameter) {
            Parameter parameter = (Parameter) node;
            if (parameter.getType() instanceof UnknownType) {
                throw new IllegalStateException("Parameter has unknown type: " + parameter);
            }
            return JavaParserFacade.get(typeSolver).convertToUsage(parameter.getType(), parameter);
        } else if (node instanceof FieldAccessExpr) {
            FieldAccessExpr fieldAccessExpr = (FieldAccessExpr) node;
            // We should understand if this is a static access
            try {
                Optional<me.tomassetti.symbolsolver.model.resolution.Value> value = new SymbolSolver(typeSolver).solveSymbolAsValue(fieldAccessExpr.getField(), fieldAccessExpr);
                if (value.isPresent()) {
                    return value.get().getUsage();
                } else {
                    throw new UnsolvedSymbolException(fieldAccessExpr.getField());
                }
            } catch (UnsolvedSymbolException e) {
                // Sure, it was not found as value because maybe it is a type and this is a static access
                if (fieldAccessExpr.getScope() instanceof NameExpr) {
                    NameExpr staticValue = (NameExpr) fieldAccessExpr.getScope();
                    SymbolReference<TypeDeclaration> typeAccessedStatically = JavaParserFactory.getContext(fieldAccessExpr, typeSolver).solveType(staticValue.toString(), typeSolver);
                    if (!typeAccessedStatically.isSolved()) {
                        throw e;
                    } else {
                        // TODO here maybe we have to substitute type typeParametersValues
                        return typeAccessedStatically.getCorrespondingDeclaration().getField(fieldAccessExpr.getField()).getType();
                    }
                } else {
                    throw e;
                }
            }
        } else if (node instanceof ObjectCreationExpr) {
            ObjectCreationExpr objectCreationExpr = (ObjectCreationExpr) node;
            Type type = JavaParserFacade.get(typeSolver).convertToUsage(objectCreationExpr.getType(), node);
            return type;
        } else if (node instanceof NullLiteralExpr) {
            return NullType.INSTANCE;
        } else if (node instanceof BooleanLiteralExpr) {
            return PrimitiveType.BOOLEAN;
        } else if (node instanceof IntegerLiteralExpr) {
            return PrimitiveType.INT;
        } else if (node instanceof LongLiteralExpr) {
            return PrimitiveType.LONG;
        } else if (node instanceof CharLiteralExpr) {
            return PrimitiveType.CHAR;
		} else if (node instanceof DoubleLiteralExpr) {
			return PrimitiveType.DOUBLE;
		} else if (node instanceof StringLiteralExpr) {
            return new ReferenceTypeImpl(new JreTypeSolver().solveType("java.lang.String"), typeSolver);
        } else if (node instanceof UnaryExpr) {
            UnaryExpr unaryExpr = (UnaryExpr) node;
            switch (unaryExpr.getOperator()) {
                case negative:
                case positive:
                    return getTypeConcrete(unaryExpr.getExpr(), solveLambdas);
                case not:
                    return PrimitiveType.BOOLEAN;
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
                    return PrimitiveType.BOOLEAN;
                case binAnd:
                case binOr:
                    return getTypeConcrete(binaryExpr.getLeft(), solveLambdas);
                default:
                    throw new UnsupportedOperationException("FOO " + binaryExpr.getOperator().name());
            }
        } else if (node instanceof VariableDeclarationExpr) {
            VariableDeclarationExpr expr = (VariableDeclarationExpr) node;
            return convertToUsage(expr.getType(), JavaParserFactory.getContext(node, typeSolver));
        } else if (node instanceof InstanceOfExpr) {
            return PrimitiveType.BOOLEAN;
        } else if (node instanceof EnclosedExpr) {
            EnclosedExpr enclosedExpr = (EnclosedExpr) node;
            return getTypeConcrete(enclosedExpr.getInner(), solveLambdas);
        } else if (node instanceof CastExpr) {
            CastExpr enclosedExpr = (CastExpr) node;
            return convertToUsage(enclosedExpr.getType(), JavaParserFactory.getContext(node, typeSolver));
        } else if (node instanceof AssignExpr) {
            AssignExpr assignExpr = (AssignExpr) node;
            return getTypeConcrete(assignExpr.getTarget(), solveLambdas);
        } else if (node instanceof ThisExpr) {
            return new ReferenceTypeImpl(getTypeDeclaration(findContainingTypeDecl(node)), typeSolver);
        } else if (node instanceof ConditionalExpr) {
            ConditionalExpr conditionalExpr = (ConditionalExpr) node;
            return getTypeConcrete(conditionalExpr.getThenExpr(), solveLambdas);
        } else if (node instanceof ArrayCreationExpr) {
            ArrayCreationExpr arrayCreationExpr = (ArrayCreationExpr) node;
            Type res = convertToUsage(arrayCreationExpr.getType(), JavaParserFactory.getContext(node, typeSolver));
            for (int i=0; i<arrayCreationExpr.getArrayCount();i++) {
                res = new ArrayType(res);
            }
            return res;
        } else if (node instanceof ArrayAccessExpr) {
            ArrayAccessExpr arrayAccessExpr = (ArrayAccessExpr) node;
            return getTypeConcrete(arrayAccessExpr.getName(), solveLambdas);
        } else if (node instanceof SuperExpr) {
            TypeDeclaration typeOfNode = getTypeDeclaration(findContainingTypeDecl(node));
            if (typeOfNode instanceof ClassDeclaration) {
                return ((ClassDeclaration)typeOfNode).getSuperClass();
            } else {
                throw new UnsupportedOperationException(node.getClass().getCanonicalName());
            }
        } else if (node instanceof ClassExpr) {
            // This implementation does not regard the actual type argument of the ClassExpr.
            return new ReferenceTypeImpl(new ReflectionClassDeclaration(Class.class, typeSolver), typeSolver);
        } else {
            throw new UnsupportedOperationException(node.getClass().getCanonicalName());
        }
    }

    private com.github.javaparser.ast.body.TypeDeclaration findContainingTypeDecl(Node node) {
        if (node instanceof ClassOrInterfaceDeclaration) {
            return (ClassOrInterfaceDeclaration) node;
        } else if (node instanceof EnumDeclaration) {
            return (EnumDeclaration) node;
        } else if (node.getParentNode() == null) {
            throw new IllegalArgumentException();
        } else {
            return findContainingTypeDecl(node.getParentNode());
        }
    }

    public Type convertToUsage(com.github.javaparser.ast.type.Type type, Node context) {
        if (type instanceof UnknownType) {
            throw new IllegalArgumentException("Unknown type");
        }
        return convertToUsage(type, JavaParserFactory.getContext(context, typeSolver));
    }

    // This is an hack around an issue in JavaParser
    private String qName(ClassOrInterfaceType classOrInterfaceType) {
        String name = classOrInterfaceType.getName();
        if (classOrInterfaceType.getScope() != null) {
            return qName(classOrInterfaceType.getScope()) + "." + name;
        } else {
            return name;
        }
    }

    public Type convertToUsage(com.github.javaparser.ast.type.Type type, Context context) {
        if (type instanceof com.github.javaparser.ast.type.ReferenceType) {
            com.github.javaparser.ast.type.ReferenceType referenceType = (com.github.javaparser.ast.type.ReferenceType) type;
            Type typeUsage = convertToUsage(referenceType.getType(), context);
            for (int i = 0; i < referenceType.getArrayCount(); i++) {
                typeUsage = new ArrayType(typeUsage);
            }
            return typeUsage;
        } else if (type instanceof ClassOrInterfaceType) {
            ClassOrInterfaceType classOrInterfaceType = (ClassOrInterfaceType) type;
            String name = qName(classOrInterfaceType);
            SymbolReference<TypeDeclaration> ref = context.solveType(name, typeSolver);
            if (!ref.isSolved()) {
                throw new UnsolvedSymbolException(name);
            }
            TypeDeclaration typeDeclaration = ref.getCorrespondingDeclaration();
            List<Type> typeParameters = Collections.emptyList();
            if (classOrInterfaceType.getTypeArgs() != null) {
                typeParameters = classOrInterfaceType.getTypeArgs().stream().map((pt) -> convertToUsage(pt, context)).collect(Collectors.toList());
            }
            if (typeDeclaration.isTypeVariable()) {
                if (typeDeclaration instanceof TypeParameterDeclaration) {
                    return new TypeParameter((TypeParameterDeclaration) typeDeclaration);
                } else {
                    JavaParserTypeVariableDeclaration javaParserTypeVariableDeclaration = (JavaParserTypeVariableDeclaration) typeDeclaration;
                    return new TypeParameter(javaParserTypeVariableDeclaration.asTypeParameter());
                }
            } else {
                return new ReferenceTypeImpl(typeDeclaration, typeParameters, typeSolver);
            }
        } else if (type instanceof com.github.javaparser.ast.type.PrimitiveType) {
            return PrimitiveType.byName(((com.github.javaparser.ast.type.PrimitiveType) type).getType().name());
        } else if (type instanceof WildcardType) {
            WildcardType wildcardType = (WildcardType) type;
            if (wildcardType.getExtends() != null && wildcardType.getSuper() == null) {
                return Wildcard.extendsBound((ReferenceTypeImpl) convertToUsage(wildcardType.getExtends(), context));
            } else if (wildcardType.getExtends() == null && wildcardType.getSuper() != null) {
                return Wildcard.extendsBound((ReferenceTypeImpl) convertToUsage(wildcardType.getSuper(), context));
            } else if (wildcardType.getExtends() == null && wildcardType.getSuper() == null) {
                return Wildcard.UNBOUNDED;
            } else {
                throw new UnsupportedOperationException();
            }
        } else if (type instanceof com.github.javaparser.ast.type.VoidType) {
            return VoidType.INSTANCE;
        } else {
            throw new UnsupportedOperationException(type.getClass().getCanonicalName());
        }
    }


    public Type convert(com.github.javaparser.ast.type.Type type, Node node) {
        return convert(type, JavaParserFactory.getContext(node, typeSolver));
    }

    public Type convert(com.github.javaparser.ast.type.Type type, Context context) {
        return convertToUsage(type, context);
    }

    public MethodUsage solveMethodAsUsage(MethodCallExpr call) {
        List<Type> params = new ArrayList<>();
        if (call.getArgs() != null) {
            for (Expression param : call.getArgs()) {
                //getTypeConcrete(Node node, boolean solveLambdas)
                try {
                    params.add(getType(param, false));
                } catch (Exception e) {
                    throw new RuntimeException(String.format("Error calculating the type of parameter %s of method call %s", param, call), e);
                }
                //params.add(getTypeConcrete(param, false));
            }
        }
        Context context = JavaParserFactory.getContext(call, typeSolver);
        Optional<MethodUsage> methodUsage = context.solveMethodAsUsage(call.getName(), params, typeSolver);
        if (!methodUsage.isPresent()) {
            throw new RuntimeException("Method '" + call.getName() + "' cannot be resolved in context "
                    + call + " (line: " + call.getRange().begin.line + ") " + context+". Parameter types: "+ params);
        }
        return methodUsage.get();
    }

    public TypeDeclaration getTypeDeclaration(ClassOrInterfaceDeclaration classOrInterfaceDeclaration) {
        if (classOrInterfaceDeclaration.isInterface()) {
            return new JavaParserInterfaceDeclaration(classOrInterfaceDeclaration, typeSolver);
        } else {
            return new JavaParserClassDeclaration(classOrInterfaceDeclaration, typeSolver);
        }
    }

    /**
     * "this" inserted in the given point, which type would have?
     */
    public Type getTypeOfThisIn(Node node) {
        // TODO consider static methods
        if (node instanceof ClassOrInterfaceDeclaration) {
            return new ReferenceTypeImpl(getTypeDeclaration((ClassOrInterfaceDeclaration) node), typeSolver);
        } else if (node instanceof EnumDeclaration) {
            JavaParserEnumDeclaration enumDeclaration = new JavaParserEnumDeclaration((EnumDeclaration) node, typeSolver);
            return new ReferenceTypeImpl(enumDeclaration, typeSolver);
        } else {
            return getTypeOfThisIn(node.getParentNode());
        }
    }

    public TypeDeclaration getTypeDeclaration(com.github.javaparser.ast.body.TypeDeclaration typeDeclaration) {
        if (typeDeclaration instanceof ClassOrInterfaceDeclaration) {
            return getTypeDeclaration((ClassOrInterfaceDeclaration) typeDeclaration);
        } else if (typeDeclaration instanceof EnumDeclaration) {
            return new JavaParserEnumDeclaration((EnumDeclaration) typeDeclaration, typeSolver);
        } else {
            throw new UnsupportedOperationException(typeDeclaration.getClass().getCanonicalName());
        }
    }
}
