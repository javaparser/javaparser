/*
 * Copyright 2016 Federico Tomassetti
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.github.javaparser.symbolsolver.javaparsermodel;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.UnknownType;
import com.github.javaparser.ast.type.WildcardType;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.*;
import com.github.javaparser.symbolsolver.logic.FunctionalInterfaceLogic;
import com.github.javaparser.symbolsolver.logic.GenericTypeInferenceLogic;
import com.github.javaparser.symbolsolver.model.declarations.*;
import com.github.javaparser.symbolsolver.model.declarations.MethodDeclaration;
import com.github.javaparser.symbolsolver.model.declarations.TypeDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.resolution.Value;
import com.github.javaparser.symbolsolver.model.methods.MethodUsage;
import com.github.javaparser.symbolsolver.model.typesystem.*;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionClassDeclaration;
import com.github.javaparser.symbolsolver.resolution.SymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JreTypeSolver;
import javaslang.Tuple2;

import java.util.*;
import java.util.logging.ConsoleHandler;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.stream.Collectors;

import static com.github.javaparser.symbolsolver.javaparser.Navigator.getParentNode;

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
            if (result.isReferenceType()) {
                result = type.asReferenceType().transformTypeParameters((tp) -> solveGenericTypes(tp, context, typeSolver));
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
        List<Type> argumentTypes = new LinkedList<>();
        List<LambdaArgumentTypePlaceholder> placeholders = new LinkedList<>();
        int i = 0;
        for (Expression parameterValue : methodCallExpr.getArgs()) {
            if (parameterValue instanceof LambdaExpr || parameterValue instanceof MethodReferenceExpr) {
                LambdaArgumentTypePlaceholder placeholder = new LambdaArgumentTypePlaceholder(i);
                argumentTypes.add(placeholder);
                placeholders.add(placeholder);
            } else {
                try {
                    argumentTypes.add(JavaParserFacade.get(typeSolver).getType(parameterValue, solveLambdas));
                } catch (UnsolvedSymbolException e) {
                    throw e;
                } catch (Exception e) {
                    throw new RuntimeException(String.format("Unable to calculate the type of a parameter of a method call. Method call: %s, Parameter: %s",
                            methodCallExpr, parameterValue), e);
                }
            }
            i++;
        }
        SymbolReference<MethodDeclaration> res = JavaParserFactory.getContext(methodCallExpr, typeSolver).solveMethod(methodCallExpr.getName(), argumentTypes, typeSolver);
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
                    MethodCallExpr methodCallExpr = (MethodCallExpr) node;
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
            return find(map, (LambdaExpr) node);
        } else {
            return Optional.empty();
        }
    }

    /**
     * For some reasons LambdaExprs are duplicate and the equals method is not implemented correctly.
     *
     * @param map
     * @return
     */
    private Optional<Type> find(Map<Node, Type> map, LambdaExpr lambdaExpr) {
        for (Node key : map.keySet()) {
            if (key instanceof LambdaExpr) {
                LambdaExpr keyLambdaExpr = (LambdaExpr) key;
                if (keyLambdaExpr.toString().equals(lambdaExpr.toString()) && getParentNode(keyLambdaExpr) == getParentNode(lambdaExpr)) {
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
        TypeExpr typeExpr = (TypeExpr) methodReferenceExpr.getScope();
        if (!(typeExpr.getType() instanceof com.github.javaparser.ast.type.ClassOrInterfaceType)) {
            throw new UnsupportedOperationException(typeExpr.getType().getClass().getCanonicalName());
        }
        ClassOrInterfaceType classOrInterfaceType = (ClassOrInterfaceType) typeExpr.getType();
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
     * Should return more like a TypeApplication: a TypeDeclaration and possible typeParametersValues or array
     * modifiers.
     *
     * @return
     */
    private Type getTypeConcrete(Node node, boolean solveLambdas) {
        if (node == null) throw new IllegalArgumentException();
        if (node instanceof NameExpr) {
            NameExpr nameExpr = (NameExpr) node;
            logger.finest("getType on name expr " + node);
            Optional<Value> value = new SymbolSolver(typeSolver).solveSymbolAsValue(nameExpr.getName(), nameExpr);
            if (!value.isPresent()) {
                throw new UnsolvedSymbolException("Solving " + node, nameExpr.getName());
            } else {
                return value.get().getType();
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
            if (getParentNode(node) instanceof MethodCallExpr) {
                MethodCallExpr callExpr = (MethodCallExpr) getParentNode(node);
                int pos = JavaParserSymbolDeclaration.getParamPos(node);
                SymbolReference<MethodDeclaration> refMethod = JavaParserFacade.get(typeSolver).solve(callExpr);
                if (!refMethod.isSolved()) {
                    throw new UnsolvedSymbolException(getParentNode(node).toString(), callExpr.getName());
                }
                logger.finest("getType on lambda expr " + refMethod.getCorrespondingDeclaration().getName());
                //logger.finest("Method param " + refMethod.getCorrespondingDeclaration().getParam(pos));
                if (solveLambdas) {

                    // The type parameter referred here should be the java.util.stream.Stream.T
                    Type result = refMethod.getCorrespondingDeclaration().getParam(pos).getType();

                    // FIXME: here we should replace the type parameters that can be resolved
                    //        for example when invoking myListOfStrings.stream().filter(s -> s.length > 0);
                    //        the MethodDeclaration of filter is:
                    //        Stream<T> filter(Predicate<? super T> predicate)
                    //        but T in this case is equal to String
                    if (callExpr.getScope().isPresent()){

                        // If it is a static call we should not try to get the type of the scope
                        boolean staticCall = false;
                        if (callExpr.getScope().get() instanceof NameExpr) {
                            NameExpr nameExpr = (NameExpr)callExpr.getScope().get();
                            try {
                                JavaParserFactory.getContext(nameExpr, typeSolver).solveType(nameExpr.getName(), typeSolver);
                                staticCall = true;
                            } catch (Exception e) {

                            }
                        }

                        if (!staticCall) {
                            Type scopeType = JavaParserFacade.get(typeSolver).getType(callExpr.getScope().get());
                            if (scopeType.isReferenceType()) {
                                result = scopeType.asReferenceType().useThisTypeParametersOnTheGivenType(result);
                            }
                        }
                    }

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
                            Map<TypeParameterDeclaration, Type> inferredTypes = GenericTypeInferenceLogic.inferGenericTypes(formalActualTypePairs);
                            for (TypeParameterDeclaration typeName : inferredTypes.keySet()) {
                                result = result.replaceTypeVariables(typeName, inferredTypes.get(typeName));
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
            if (getParentNode(node) instanceof MethodCallExpr) {
                MethodCallExpr callExpr = (MethodCallExpr) getParentNode(node);
                int pos = JavaParserSymbolDeclaration.getParamPos(node);
                SymbolReference<MethodDeclaration> refMethod = JavaParserFacade.get(typeSolver).solve(callExpr, false);
                if (!refMethod.isSolved()) {
                    throw new UnsolvedSymbolException(getParentNode(node).toString(), callExpr.getName());
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
                            Map<TypeParameterDeclaration, Type> inferredTypes = GenericTypeInferenceLogic.inferGenericTypes(formalActualTypePairs);
                            for (TypeParameterDeclaration typeName : inferredTypes.keySet()) {
                                result = result.replaceTypeVariables(typeName, inferredTypes.get(typeName));
                            }

                        } else {
                            LambdaExpr lambdaExpr = (LambdaExpr) node;

                            List<Tuple2<Type, Type>> formalActualTypePairs = new ArrayList<>();
                            if (lambdaExpr.getBody() instanceof ExpressionStmt) {
                                ExpressionStmt expressionStmt = (ExpressionStmt) lambdaExpr.getBody();
                                Type actualType = getType(expressionStmt.getExpression());
                                Type formalType = functionalMethod.get().returnType();
                                formalActualTypePairs.add(new Tuple2<>(formalType, actualType));
                                Map<TypeParameterDeclaration, Type> inferredTypes = GenericTypeInferenceLogic.inferGenericTypes(formalActualTypePairs);
                                for (TypeParameterDeclaration typeName : inferredTypes.keySet()) {
                                    result = result.replaceTypeVariables(typeName, inferredTypes.get(typeName));
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
            if (getParentNode(node) instanceof FieldDeclaration) {
                FieldDeclaration parent = (FieldDeclaration) getParentNode(node);
                return JavaParserFacade.get(typeSolver).convertToUsageVariableType((VariableDeclarator) node);
            } else if (getParentNode(node) instanceof VariableDeclarationExpr) {
                VariableDeclarationExpr parent = (VariableDeclarationExpr) getParentNode(node);
                return JavaParserFacade.get(typeSolver).convertToUsageVariableType((VariableDeclarator) node);
            } else {
                throw new UnsupportedOperationException(getParentNode(node).getClass().getCanonicalName());
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
            if (fieldAccessExpr.getScope() instanceof NameExpr) {
                NameExpr staticValue = (NameExpr) fieldAccessExpr.getScope();
                SymbolReference<TypeDeclaration> typeAccessedStatically = JavaParserFactory.getContext(fieldAccessExpr, typeSolver).solveType(staticValue.toString(), typeSolver);
                if (typeAccessedStatically.isSolved()) {
                    // TODO here maybe we have to substitute type typeParametersValues
                    return typeAccessedStatically.getCorrespondingDeclaration().getField(fieldAccessExpr.getField()).getType();
                }
            }
            Optional<Value> value = new SymbolSolver(typeSolver).solveSymbolAsValue(fieldAccessExpr.getField(), fieldAccessExpr);
            if (value.isPresent()) {
                return value.get().getType();
            } else {
                throw new UnsolvedSymbolException(fieldAccessExpr.getField());
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
                case postIncrement:
                case preIncrement:
                case preDecrement:
                case postDecrement:
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
            if (expr.getVariables().size() != 1) {
                throw new UnsupportedOperationException();
            }
            return convertToUsageVariableType(expr.getVariables().get(0));
        } else if (node instanceof InstanceOfExpr) {
            return PrimitiveType.BOOLEAN;
        } else if (node instanceof EnclosedExpr) {
            EnclosedExpr enclosedExpr = (EnclosedExpr) node;
            return getTypeConcrete(enclosedExpr.getInner().get(), solveLambdas);
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
            return res;
        } else if (node instanceof ArrayAccessExpr) {
            ArrayAccessExpr arrayAccessExpr = (ArrayAccessExpr) node;
            return getTypeConcrete(arrayAccessExpr.getName(), solveLambdas);
        } else if (node instanceof SuperExpr) {
            TypeDeclaration typeOfNode = getTypeDeclaration(findContainingTypeDecl(node));
            if (typeOfNode instanceof ClassDeclaration) {
                return ((ClassDeclaration) typeOfNode).getSuperClass();
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
        } else if (getParentNode(node) == null) {
            throw new IllegalArgumentException();
        } else {
            return findContainingTypeDecl(getParentNode(node));
        }
    }

    public Type convertToUsageVariableType(VariableDeclarator var) {
        Type type = JavaParserFacade.get(typeSolver).convertToUsage(var.getType(), var);
        return type;
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
        if (classOrInterfaceType.getScope().isPresent()) {
            return qName(classOrInterfaceType.getScope().get()) + "." + name;
        } else {
            return name;
        }
    }

    public Type convertToUsage(com.github.javaparser.ast.type.Type type, Context context) {
        if (type instanceof ClassOrInterfaceType) {
            ClassOrInterfaceType classOrInterfaceType = (ClassOrInterfaceType) type;
            String name = qName(classOrInterfaceType);
            SymbolReference<TypeDeclaration> ref = context.solveType(name, typeSolver);
            if (!ref.isSolved()) {
                throw new UnsolvedSymbolException(name);
            }
            TypeDeclaration typeDeclaration = ref.getCorrespondingDeclaration();
            List<Type> typeParameters = Collections.emptyList();
            if (classOrInterfaceType.getTypeArguments().isPresent()) {
                typeParameters = classOrInterfaceType.getTypeArguments().get().stream().map((pt) -> convertToUsage(pt, context)).collect(Collectors.toList());
            }
            if (typeDeclaration.isTypeParameter()) {
                if (typeDeclaration instanceof TypeParameterDeclaration) {
                    return new TypeVariable((TypeParameterDeclaration) typeDeclaration);
                } else {
                    JavaParserTypeVariableDeclaration javaParserTypeVariableDeclaration = (JavaParserTypeVariableDeclaration) typeDeclaration;
                    return new TypeVariable(javaParserTypeVariableDeclaration.asTypeParameter());
                }
            } else {
                return new ReferenceTypeImpl(typeDeclaration, typeParameters, typeSolver);
            }
        } else if (type instanceof com.github.javaparser.ast.type.PrimitiveType) {
            return PrimitiveType.byName(((com.github.javaparser.ast.type.PrimitiveType) type).getType().name());
        } else if (type instanceof WildcardType) {
            WildcardType wildcardType = (WildcardType) type;
            if (wildcardType.getExtends().isPresent() && !wildcardType.getSuper().isPresent()) {
                return Wildcard.extendsBound((ReferenceTypeImpl) convertToUsage(wildcardType.getExtends().get(), context));
            } else if (!wildcardType.getExtends().isPresent() && wildcardType.getSuper().isPresent()) {
                return Wildcard.extendsBound((ReferenceTypeImpl) convertToUsage(wildcardType.getSuper().get(), context));
            } else if (!wildcardType.getExtends().isPresent() && !wildcardType.getSuper().isPresent()) {
                return Wildcard.UNBOUNDED;
            } else {
                throw new UnsupportedOperationException(wildcardType.toString());
            }
        } else if (type instanceof com.github.javaparser.ast.type.VoidType) {
            return VoidType.INSTANCE;
        } else if (type instanceof com.github.javaparser.ast.type.ArrayType) {
            com.github.javaparser.ast.type.ArrayType jpArrayType = (com.github.javaparser.ast.type.ArrayType) type;
            return new ArrayType(convertToUsage(jpArrayType.getComponentType(), context));
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
                    + call + " (line: " + call.getRange().begin.line + ") " + context + ". Parameter types: " + params);
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
            return getTypeOfThisIn(getParentNode(node));
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
