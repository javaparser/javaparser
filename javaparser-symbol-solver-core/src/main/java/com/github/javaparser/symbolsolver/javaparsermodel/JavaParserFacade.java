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

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.ExplicitConstructorInvocationStmt;
import com.github.javaparser.ast.type.*;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.types.*;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.FieldAccessContext;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.*;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.*;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionClassDeclaration;
import com.github.javaparser.symbolsolver.resolution.ConstructorResolutionLogic;
import com.github.javaparser.symbolsolver.resolution.SymbolSolver;

import java.util.*;
import java.util.logging.ConsoleHandler;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.stream.Collectors;

import static com.github.javaparser.symbolsolver.javaparser.Navigator.requireParentNode;

/**
 * Class to be used by final users to solve symbols for JavaParser ASTs.
 *
 * @author Federico Tomassetti
 */
public class JavaParserFacade {

    private static Logger logger = Logger.getLogger(JavaParserFacade.class.getCanonicalName());

    static {
        logger.setLevel(Level.INFO);
        ConsoleHandler consoleHandler = new ConsoleHandler();
        consoleHandler.setLevel(Level.INFO);
        logger.addHandler(consoleHandler);
    }

    private static Map<TypeSolver, JavaParserFacade> instances = new WeakHashMap<>();
    private TypeSolver typeSolver;
    private SymbolSolver symbolSolver;
    private Map<Node, ResolvedType> cacheWithLambdasSolved = new IdentityHashMap<>();
    private Map<Node, ResolvedType> cacheWithoutLambdasSolved = new IdentityHashMap<>();
    private TypeExtractor typeExtractor;

    private JavaParserFacade(TypeSolver typeSolver) {
        this.typeSolver = typeSolver.getRoot();
        this.symbolSolver = new SymbolSolver(typeSolver);
        this.typeExtractor = new TypeExtractor(typeSolver, this);
    }

    public TypeSolver getTypeSolver() {
        return typeSolver;
    }

    public SymbolSolver getSymbolSolver() {
        return symbolSolver;
    }

    public static JavaParserFacade get(TypeSolver typeSolver) {
        return instances.computeIfAbsent(typeSolver, JavaParserFacade::new);
    }

    /**
     * This method is used to clear internal caches for the sake of releasing memory.
     */
    public static void clearInstances() {
        instances.clear();
    }

    protected static ResolvedType solveGenericTypes(ResolvedType type, Context context, TypeSolver typeSolver) {
        if (type.isTypeVariable()) {
            return context.solveGenericType(type.describe(), typeSolver).orElse(type);
        }
        if (type.isWildcard()) {
            if (type.asWildcard().isExtends() || type.asWildcard().isSuper()) {
                ResolvedWildcard wildcardUsage = type.asWildcard();
                ResolvedType boundResolved = solveGenericTypes(wildcardUsage.getBoundedType(), context, typeSolver);
                if (wildcardUsage.isExtends()) {
                    return ResolvedWildcard.extendsBound(boundResolved);
                } else {
                    return ResolvedWildcard.superBound(boundResolved);
                }
            }
        }
        return type;
    }

    public SymbolReference<? extends ResolvedValueDeclaration> solve(NameExpr nameExpr) {
        return symbolSolver.solveSymbol(nameExpr.getName().getId(), nameExpr);
    }

    public SymbolReference<? extends ResolvedValueDeclaration> solve(SimpleName nameExpr) {
        return symbolSolver.solveSymbol(nameExpr.getId(), nameExpr);
    }

    public SymbolReference<? extends ResolvedValueDeclaration> solve(Expression expr) {
        return expr.toNameExpr().map(this::solve).orElseThrow(() -> new IllegalArgumentException(expr.getClass().getCanonicalName()));
    }

    public SymbolReference<ResolvedMethodDeclaration> solve(MethodCallExpr methodCallExpr) {
        return solve(methodCallExpr, true);
    }

    public SymbolReference<ResolvedConstructorDeclaration> solve(ObjectCreationExpr objectCreationExpr) {
        return solve(objectCreationExpr, true);
    }

    public SymbolReference<ResolvedConstructorDeclaration> solve(ExplicitConstructorInvocationStmt explicitConstructorInvocationStmt) {
        return solve(explicitConstructorInvocationStmt, true);
    }

    public SymbolReference<ResolvedConstructorDeclaration> solve(ExplicitConstructorInvocationStmt explicitConstructorInvocationStmt, boolean solveLambdas) {
        List<ResolvedType> argumentTypes = new LinkedList<>();
        List<LambdaArgumentTypePlaceholder> placeholders = new LinkedList<>();

        solveArguments(explicitConstructorInvocationStmt, explicitConstructorInvocationStmt.getArguments(), solveLambdas, argumentTypes, placeholders);

        Optional<ClassOrInterfaceDeclaration> optAncestor = explicitConstructorInvocationStmt.getAncestorOfType(ClassOrInterfaceDeclaration.class);
        if (!optAncestor.isPresent()) {
            return SymbolReference.unsolved(ResolvedConstructorDeclaration.class);
        }
        ClassOrInterfaceDeclaration classNode = optAncestor.get();
        ResolvedTypeDeclaration typeDecl = null;
        if (!explicitConstructorInvocationStmt.isThis()) {
            ResolvedType classDecl = JavaParserFacade.get(typeSolver).convert(classNode.getExtendedTypes(0), classNode);
            if (classDecl.isReferenceType()) {
                typeDecl = classDecl.asReferenceType().getTypeDeclaration();
            }
        } else {
            SymbolReference<ResolvedTypeDeclaration> sr = JavaParserFactory.getContext(classNode, typeSolver).solveType(classNode.getNameAsString(), typeSolver);
            if (sr.isSolved()) {
                typeDecl = sr.getCorrespondingDeclaration();
            }
        }
        if (typeDecl == null) {
            return SymbolReference.unsolved(ResolvedConstructorDeclaration.class);
        }
        SymbolReference<ResolvedConstructorDeclaration> res = ConstructorResolutionLogic.findMostApplicable(((ResolvedClassDeclaration) typeDecl).getConstructors(), argumentTypes, typeSolver);
        for (LambdaArgumentTypePlaceholder placeholder : placeholders) {
            placeholder.setMethod(res);
        }
        return res;
    }

    public SymbolReference<ResolvedTypeDeclaration> solve(ThisExpr node) {
        // If 'this' is prefixed by a class eg. MyClass.this
        if (node.getClassExpr().isPresent()) {
            // Get the class name
            String className = node.getClassExpr().get().toString();
            // Attempt to resolve using a typeSolver
            SymbolReference<ResolvedReferenceTypeDeclaration> clazz = typeSolver.tryToSolveType(className);
            if (clazz.isSolved()) {
                return SymbolReference.solved(clazz.getCorrespondingDeclaration());
            }
            // Attempt to resolve locally in Compilation unit
            Optional<CompilationUnit> cu = node.getAncestorOfType(CompilationUnit.class);
            if (cu.isPresent()) {
                Optional<ClassOrInterfaceDeclaration> classByName = cu.get().getClassByName(className);
                if (classByName.isPresent()) {
                    return SymbolReference.solved(getTypeDeclaration(classByName.get()));
                }
            }
        }
        return SymbolReference.solved(getTypeDeclaration(findContainingTypeDeclOrObjectCreationExpr(node)));
    }

    /**
     * Given a constructor call find out to which constructor declaration it corresponds.
     */
    public SymbolReference<ResolvedConstructorDeclaration> solve(ObjectCreationExpr objectCreationExpr, boolean solveLambdas) {
        List<ResolvedType> argumentTypes = new LinkedList<>();
        List<LambdaArgumentTypePlaceholder> placeholders = new LinkedList<>();

        solveArguments(objectCreationExpr, objectCreationExpr.getArguments(), solveLambdas, argumentTypes, placeholders);

        ResolvedType classDecl = JavaParserFacade.get(typeSolver).convert(objectCreationExpr.getType(), objectCreationExpr);
        if (!classDecl.isReferenceType()) {
            return SymbolReference.unsolved(ResolvedConstructorDeclaration.class);
        }
        SymbolReference<ResolvedConstructorDeclaration> res = ConstructorResolutionLogic.findMostApplicable(((ResolvedClassDeclaration) classDecl.asReferenceType().getTypeDeclaration()).getConstructors(), argumentTypes, typeSolver);
        for (LambdaArgumentTypePlaceholder placeholder : placeholders) {
            placeholder.setMethod(res);
        }
        return res;
    }

    private void solveArguments(Node node, NodeList<Expression> args, boolean solveLambdas, List<ResolvedType> argumentTypes,
                                List<LambdaArgumentTypePlaceholder> placeholders) {
        int i = 0;
        for (Expression parameterValue : args) {
            if (parameterValue instanceof LambdaExpr || parameterValue instanceof MethodReferenceExpr) {
                LambdaArgumentTypePlaceholder placeholder = new LambdaArgumentTypePlaceholder(i);
                argumentTypes.add(placeholder);
                placeholders.add(placeholder);
            } else {
                try {
                    argumentTypes.add(JavaParserFacade.get(typeSolver).getType(parameterValue, solveLambdas));
                } catch (com.github.javaparser.resolution.UnsolvedSymbolException e) {
                    throw e;
                } catch (Exception e) {
                    throw new RuntimeException(String.format("Unable to calculate the type of a parameter of a method call. Method call: %s, Parameter: %s",
                            node, parameterValue), e);
                }
            }
            i++;
        }
    }

    /**
     * Given a method call find out to which method declaration it corresponds.
     */
    public SymbolReference<ResolvedMethodDeclaration> solve(MethodCallExpr methodCallExpr, boolean solveLambdas) {
        List<ResolvedType> argumentTypes = new LinkedList<>();
        List<LambdaArgumentTypePlaceholder> placeholders = new LinkedList<>();

        solveArguments(methodCallExpr, methodCallExpr.getArguments(), solveLambdas, argumentTypes, placeholders);

        SymbolReference<ResolvedMethodDeclaration> res = JavaParserFactory.getContext(methodCallExpr, typeSolver).solveMethod(methodCallExpr.getName().getId(), argumentTypes, false, typeSolver);
        for (LambdaArgumentTypePlaceholder placeholder : placeholders) {
            placeholder.setMethod(res);
        }
        return res;
    }

    public SymbolReference<ResolvedAnnotationDeclaration> solve(AnnotationExpr annotationExpr) {
        Context context = JavaParserFactory.getContext(annotationExpr, typeSolver);
        SymbolReference<ResolvedTypeDeclaration> typeDeclarationSymbolReference = context.solveType(annotationExpr.getNameAsString(), typeSolver);
        ResolvedAnnotationDeclaration annotationDeclaration = (ResolvedAnnotationDeclaration) typeDeclarationSymbolReference.getCorrespondingDeclaration();
        if (typeDeclarationSymbolReference.isSolved()) {
            return SymbolReference.solved(annotationDeclaration);
        } else {
            return SymbolReference.unsolved(ResolvedAnnotationDeclaration.class);
        }
    }

    public SymbolReference<ResolvedFieldDeclaration> solve(FieldAccessExpr fieldAccessExpr) {
        return ((FieldAccessContext) JavaParserFactory.getContext(fieldAccessExpr, typeSolver)).solveField(fieldAccessExpr.getName().getId(), typeSolver);
    }

    public ResolvedType getType(Node node) {
        return getType(node, true);
    }

    public ResolvedType getType(Node node, boolean solveLambdas) {
        if (solveLambdas) {
            if (!cacheWithLambdasSolved.containsKey(node)) {
                ResolvedType res = getTypeConcrete(node, solveLambdas);

                cacheWithLambdasSolved.put(node, res);

                boolean secondPassNecessary = false;
                if (node instanceof MethodCallExpr) {
                    MethodCallExpr methodCallExpr = (MethodCallExpr) node;
                    for (Node arg : methodCallExpr.getArguments()) {
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
            Optional<ResolvedType> res = find(cacheWithLambdasSolved, node);
            if (res.isPresent()) {
                return res.get();
            }
            res = find(cacheWithoutLambdasSolved, node);
            if (!res.isPresent()) {
                ResolvedType resType = getTypeConcrete(node, solveLambdas);
                cacheWithoutLambdasSolved.put(node, resType);
                logger.finer("getType on " + node + " (no solveLambdas) -> " + res);
                return resType;
            }
            return res.get();
        }
    }

    private Optional<ResolvedType> find(Map<Node, ResolvedType> map, Node node) {
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
     */
    private Optional<ResolvedType> find(Map<Node, ResolvedType> map, LambdaExpr lambdaExpr) {
        for (Node key : map.keySet()) {
            if (key instanceof LambdaExpr) {
                LambdaExpr keyLambdaExpr = (LambdaExpr) key;
                if (keyLambdaExpr.toString().equals(lambdaExpr.toString()) && requireParentNode(keyLambdaExpr) == requireParentNode(lambdaExpr)) {
                    return Optional.of(map.get(keyLambdaExpr));
                }
            }
        }
        return Optional.empty();
    }

    protected MethodUsage toMethodUsage(MethodReferenceExpr methodReferenceExpr) {
        if (!(methodReferenceExpr.getScope() instanceof TypeExpr)) {
            throw new UnsupportedOperationException();
        }
        TypeExpr typeExpr = (TypeExpr) methodReferenceExpr.getScope();
        if (!(typeExpr.getType() instanceof com.github.javaparser.ast.type.ClassOrInterfaceType)) {
            throw new UnsupportedOperationException(typeExpr.getType().getClass().getCanonicalName());
        }
        ClassOrInterfaceType classOrInterfaceType = (ClassOrInterfaceType) typeExpr.getType();
        SymbolReference<ResolvedTypeDeclaration> typeDeclarationSymbolReference = JavaParserFactory.getContext(classOrInterfaceType, typeSolver).solveType(classOrInterfaceType.getName().getId(), typeSolver);
        if (!typeDeclarationSymbolReference.isSolved()) {
            throw new UnsupportedOperationException();
        }
        List<MethodUsage> methodUsages = ((ResolvedReferenceTypeDeclaration) typeDeclarationSymbolReference.getCorrespondingDeclaration()).getAllMethods().stream().filter(it -> it.getName().equals(methodReferenceExpr.getIdentifier())).collect(Collectors.toList());
        switch (methodUsages.size()) {
            case 0:
                throw new UnsupportedOperationException();
            case 1:
                return methodUsages.get(0);
            default:
                throw new UnsupportedOperationException();
        }
    }

    protected ResolvedType getBinaryTypeConcrete(Node left, Node right, boolean solveLambdas) {
        ResolvedType leftType = getTypeConcrete(left, solveLambdas);
        ResolvedType rightType = getTypeConcrete(right, solveLambdas);
        if (rightType.isAssignableBy(leftType)) {
            return rightType;
        }
        return leftType;
    }


    /**
     * Should return more like a TypeApplication: a TypeDeclaration and possible typeParametersValues or array
     * modifiers.
     */
    private ResolvedType getTypeConcrete(Node node, boolean solveLambdas) {
        if (node == null) throw new IllegalArgumentException();
        return node.accept(typeExtractor, solveLambdas);
    }

    protected com.github.javaparser.ast.body.TypeDeclaration<?> findContainingTypeDecl(Node node) {
        if (node instanceof ClassOrInterfaceDeclaration) {
            return (ClassOrInterfaceDeclaration) node;
        }
        if (node instanceof EnumDeclaration) {
            return (EnumDeclaration) node;
        }
        return findContainingTypeDecl(requireParentNode(node));

    }

    protected Node findContainingTypeDeclOrObjectCreationExpr(Node node) {
        if (node instanceof ClassOrInterfaceDeclaration) {
            return node;
        }
        if (node instanceof EnumDeclaration) {
            return node;
        }
        Node parent = requireParentNode(node);
        if (parent instanceof ObjectCreationExpr && !((ObjectCreationExpr) parent).getArguments().contains(node)) {
            return parent;
        }
        return findContainingTypeDeclOrObjectCreationExpr(parent);
    }

    public ResolvedType convertToUsageVariableType(VariableDeclarator var) {
        return get(typeSolver).convertToUsage(var.getType(), var);
    }

    public ResolvedType convertToUsage(com.github.javaparser.ast.type.Type type, Node context) {
        if (type.isUnknownType()) {
            throw new IllegalArgumentException("Inferred lambda parameter type");
        }
        return convertToUsage(type, JavaParserFactory.getContext(context, typeSolver));
    }

    public ResolvedType convertToUsage(com.github.javaparser.ast.type.Type type) {
        return convertToUsage(type, type);
    }

    // This is an hack around an issue in JavaParser
    private String qName(ClassOrInterfaceType classOrInterfaceType) {
        String name = classOrInterfaceType.getName().getId();
        if (classOrInterfaceType.getScope().isPresent()) {
            return qName(classOrInterfaceType.getScope().get()) + "." + name;
        }
        return name;
    }

    protected ResolvedType convertToUsage(com.github.javaparser.ast.type.Type type, Context context) {
        if (context == null) {
            throw new NullPointerException("Context should not be null");
        }
        if (type instanceof ClassOrInterfaceType) {
            ClassOrInterfaceType classOrInterfaceType = (ClassOrInterfaceType) type;
            String name = qName(classOrInterfaceType);
            SymbolReference<ResolvedTypeDeclaration> ref = context.solveType(name, typeSolver);
            if (!ref.isSolved()) {
                throw new UnsolvedSymbolException(name);
            }
            ResolvedTypeDeclaration typeDeclaration = ref.getCorrespondingDeclaration();
            List<ResolvedType> typeParameters = Collections.emptyList();
            if (classOrInterfaceType.getTypeArguments().isPresent()) {
                typeParameters = classOrInterfaceType.getTypeArguments().get().stream().map((pt) -> convertToUsage(pt, context)).collect(Collectors.toList());
            }
            if (typeDeclaration.isTypeParameter()) {
                if (typeDeclaration instanceof ResolvedTypeParameterDeclaration) {
                    return new ResolvedTypeVariable((ResolvedTypeParameterDeclaration) typeDeclaration);
                } else {
                    JavaParserTypeVariableDeclaration javaParserTypeVariableDeclaration = (JavaParserTypeVariableDeclaration) typeDeclaration;
                    return new ResolvedTypeVariable(javaParserTypeVariableDeclaration.asTypeParameter());
                }
            } else {
                return new ReferenceTypeImpl((ResolvedReferenceTypeDeclaration) typeDeclaration, typeParameters, typeSolver);
            }
        } else if (type instanceof com.github.javaparser.ast.type.PrimitiveType) {
            return ResolvedPrimitiveType.byName(((com.github.javaparser.ast.type.PrimitiveType) type).getType().name());
        } else if (type instanceof WildcardType) {
            WildcardType wildcardType = (WildcardType) type;
            if (wildcardType.getExtendedType().isPresent() && !wildcardType.getSuperType().isPresent()) {
                return ResolvedWildcard.extendsBound(convertToUsage(wildcardType.getExtendedType().get(), context)); // removed (ReferenceTypeImpl)
            } else if (!wildcardType.getExtendedType().isPresent() && wildcardType.getSuperType().isPresent()) {
                return ResolvedWildcard.superBound(convertToUsage(wildcardType.getSuperType().get(), context)); // removed (ReferenceTypeImpl)
            } else if (!wildcardType.getExtendedType().isPresent() && !wildcardType.getSuperType().isPresent()) {
                return ResolvedWildcard.UNBOUNDED;
            } else {
                throw new UnsupportedOperationException(wildcardType.toString());
            }
        } else if (type instanceof com.github.javaparser.ast.type.VoidType) {
            return ResolvedVoidType.INSTANCE;
        } else if (type instanceof com.github.javaparser.ast.type.ArrayType) {
            com.github.javaparser.ast.type.ArrayType jpArrayType = (com.github.javaparser.ast.type.ArrayType) type;
            return new ResolvedArrayType(convertToUsage(jpArrayType.getComponentType(), context));
        } else if (type instanceof UnionType) {
            UnionType unionType = (UnionType) type;
            return new ResolvedUnionType(unionType.getElements().stream().map(el -> convertToUsage(el, context)).collect(Collectors.toList()));
        } else {
            throw new UnsupportedOperationException(type.getClass().getCanonicalName());
        }
    }


    public ResolvedType convert(Type type, Node node) {
        return convert(type, JavaParserFactory.getContext(node, typeSolver));
    }

    public ResolvedType convert(com.github.javaparser.ast.type.Type type, Context context) {
        return convertToUsage(type, context);
    }

    public MethodUsage solveMethodAsUsage(MethodCallExpr call) {
        List<ResolvedType> params = new ArrayList<>();
        if (call.getArguments() != null) {
            for (Expression param : call.getArguments()) {
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
        Optional<MethodUsage> methodUsage = context.solveMethodAsUsage(call.getName().getId(), params, typeSolver);
        if (!methodUsage.isPresent()) {
            throw new RuntimeException("Method '" + call.getName() + "' cannot be resolved in context "
                    + call + " (line: " + call.getRange().map(r -> "" + r.begin.line).orElse("??") + ") " + context + ". Parameter types: " + params);
        }
        return methodUsage.get();
    }

    public ResolvedReferenceTypeDeclaration getTypeDeclaration(Node node) {
        if (node instanceof TypeDeclaration) {
            return getTypeDeclaration((TypeDeclaration) node);
        } else if (node instanceof ObjectCreationExpr) {
            return new JavaParserAnonymousClassDeclaration((ObjectCreationExpr) node, typeSolver);
        } else {
            throw new IllegalArgumentException();
        }
    }

    public ResolvedReferenceTypeDeclaration getTypeDeclaration(ClassOrInterfaceDeclaration classOrInterfaceDeclaration) {
        return JavaParserFactory.toTypeDeclaration(classOrInterfaceDeclaration, typeSolver);
    }

    /**
     * "this" inserted in the given point, which type would have?
     */
    public ResolvedType getTypeOfThisIn(Node node) {
        // TODO consider static methods
        if (node instanceof ClassOrInterfaceDeclaration) {
            return new ReferenceTypeImpl(getTypeDeclaration((ClassOrInterfaceDeclaration) node), typeSolver);
        } else if (node instanceof EnumDeclaration) {
            JavaParserEnumDeclaration enumDeclaration = new JavaParserEnumDeclaration((EnumDeclaration) node, typeSolver);
            return new ReferenceTypeImpl(enumDeclaration, typeSolver);
        } else if (node instanceof ObjectCreationExpr && ((ObjectCreationExpr) node).getAnonymousClassBody().isPresent()) {
            JavaParserAnonymousClassDeclaration anonymousDeclaration = new JavaParserAnonymousClassDeclaration((ObjectCreationExpr) node, typeSolver);
            return new ReferenceTypeImpl(anonymousDeclaration, typeSolver);
        }
        return getTypeOfThisIn(requireParentNode(node));
    }

    public ResolvedReferenceTypeDeclaration getTypeDeclaration(com.github.javaparser.ast.body.TypeDeclaration<?> typeDeclaration) {
        return JavaParserFactory.toTypeDeclaration(typeDeclaration, typeSolver);
    }

    public ResolvedType classToResolvedType(Class<?> clazz) {
        if (clazz.isPrimitive()) {
            return ResolvedPrimitiveType.byName(clazz.getName());
        }
        return new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeSolver), typeSolver);
    }
}
