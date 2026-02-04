/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2026 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */

package com.github.javaparser.symbolsolver.javaparsermodel;

import static com.github.javaparser.resolution.Navigator.demandParentNode;
import static com.github.javaparser.resolution.model.SymbolReference.solved;
import static com.github.javaparser.resolution.model.SymbolReference.unsolved;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.DataKey;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.ExplicitConstructorInvocationStmt;
import com.github.javaparser.ast.stmt.ForEachStmt;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.resolution.*;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.logic.ConstructorResolutionLogic;
import com.github.javaparser.resolution.logic.MethodResolutionLogic;
import com.github.javaparser.resolution.model.LambdaArgumentTypePlaceholder;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.FieldAccessContext;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserAnonymousClassDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserEnumDeclaration;
import com.github.javaparser.symbolsolver.resolution.SymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.github.javaparser.utils.Log;
import java.util.*;
import java.util.stream.Collectors;

/**
 * Class to be used by final users to solve symbols for JavaParser ASTs.
 *
 * @author Federico Tomassetti
 */
public class JavaParserFacade {

    // Start of static class

    private static final DataKey<ResolvedType> TYPE_WITH_LAMBDAS_RESOLVED = new DataKey<ResolvedType>() {};
    private static final DataKey<ResolvedType> TYPE_WITHOUT_LAMBDAS_RESOLVED = new DataKey<ResolvedType>() {};

    private static final Map<TypeSolver, JavaParserFacade> instances = new WeakHashMap<>();

    private static final String JAVA_LANG_STRING = String.class.getCanonicalName();

    /**
     * Note that the addition of the modifier {@code synchronized} is specific and directly in response to issue #2668.
     * <br>This <strong>MUST NOT</strong> be misinterpreted as a signal that JavaParser is safe to use within a multi-threaded environment.
     * <br>
     * <br>Additional discussion and context from a user attempting multithreading can be found within issue #2671 .
     * <br>
     *
     * @see <a href="https://github.com/javaparser/javaparser/issues/2668">https://github.com/javaparser/javaparser/issues/2668</a>
     * @see <a href="https://github.com/javaparser/javaparser/issues/2671">https://github.com/javaparser/javaparser/issues/2671</a>
     */
    public static synchronized JavaParserFacade get(TypeSolver typeSolver) {
        return instances.computeIfAbsent(typeSolver.getRoot(), JavaParserFacade::new);
    }

    /**
     * This method is used to clear internal caches for the sake of releasing memory.
     */
    public static void clearInstances() {
        instances.clear();
    }

    // End of static class

    private final TypeSolver typeSolver;
    private final TypeExtractor typeExtractor;
    private final Solver symbolSolver;
    private final SymbolResolver symbolResolver;

    private FailureHandler failureHandler;

    private JavaParserFacade(TypeSolver typeSolver) {
        this.typeSolver = typeSolver.getRoot();
        this.symbolSolver = new SymbolSolver(typeSolver);
        this.typeExtractor = new TypeExtractor(this.typeSolver, this);
        this.failureHandler = new FailureHandler();
        this.symbolResolver = new JavaSymbolSolver(this.typeSolver);
    }

    public TypeSolver getTypeSolver() {
        return typeSolver;
    }

    public Solver getSymbolSolver() {
        return symbolSolver;
    }

    public SymbolReference<? extends ResolvedValueDeclaration> solve(NameExpr nameExpr) {
        return symbolSolver.solveSymbol(nameExpr.getName().getId(), nameExpr);
    }

    public SymbolReference<? extends ResolvedValueDeclaration> solve(SimpleName nameExpr) {
        return symbolSolver.solveSymbol(nameExpr.getId(), nameExpr);
    }

    public SymbolReference<? extends ResolvedValueDeclaration> solve(Expression expr) {
        return expr.toNameExpr()
                .map(this::solve)
                .orElseThrow(() -> new IllegalArgumentException(expr.getClass().getCanonicalName()));
    }

    public SymbolReference<ResolvedMethodDeclaration> solve(MethodCallExpr methodCallExpr) {
        return solve(methodCallExpr, true);
    }

    public SymbolReference<ResolvedMethodDeclaration> solve(MethodReferenceExpr methodReferenceExpr) {
        return solve(methodReferenceExpr, true);
    }

    public SymbolReference<ResolvedConstructorDeclaration> solve(ObjectCreationExpr objectCreationExpr) {
        return solve(objectCreationExpr, true);
    }

    public SymbolReference<ResolvedConstructorDeclaration> solve(
            ExplicitConstructorInvocationStmt explicitConstructorInvocationStmt) {
        return solve(explicitConstructorInvocationStmt, true);
    }

    public SymbolReference<ResolvedConstructorDeclaration> solve(
            ExplicitConstructorInvocationStmt explicitConstructorInvocationStmt, boolean solveLambdas) {
        // Constructor invocation must exist within a class (not interface).
        Optional<ClassOrInterfaceDeclaration> optAncestorClassOrInterfaceNode =
                explicitConstructorInvocationStmt.findAncestor(ClassOrInterfaceDeclaration.class);
        if (!optAncestorClassOrInterfaceNode.isPresent()) {
            return unsolved();
        }

        ClassOrInterfaceDeclaration classOrInterfaceNode = optAncestorClassOrInterfaceNode.get();
        ResolvedReferenceTypeDeclaration resolvedClassNode = classOrInterfaceNode.resolve();
        if (!resolvedClassNode.isClass()) {
            throw new IllegalStateException(
                    "Expected to be a class -- cannot call this() or super() within an interface.");
        }

        ResolvedTypeDeclaration typeDecl = null;
        if (explicitConstructorInvocationStmt.isThis()) {
            // this()
            typeDecl = resolvedClassNode.asReferenceType();
        } else {
            // super()
            Optional<ResolvedReferenceType> superClass =
                    resolvedClassNode.asClass().getSuperClass();
            if (superClass.isPresent() && superClass.get().getTypeDeclaration().isPresent()) {
                typeDecl = superClass.get().getTypeDeclaration().get();
            }
        }
        if (typeDecl == null) {
            return unsolved();
        }

        // Solve each of the arguments being passed into this constructor invocation.
        List<ResolvedType> argumentTypes = new LinkedList<>();
        List<LambdaArgumentTypePlaceholder> placeholders = new LinkedList<>();
        solveArguments(
                explicitConstructorInvocationStmt,
                explicitConstructorInvocationStmt.getArguments(),
                solveLambdas,
                argumentTypes,
                placeholders);

        // Determine which constructor is referred to, and return it.
        SymbolReference<ResolvedConstructorDeclaration> res = ConstructorResolutionLogic.findMostApplicable(
                ((ResolvedClassDeclaration) typeDecl).getConstructors(), argumentTypes, typeSolver);
        for (LambdaArgumentTypePlaceholder placeholder : placeholders) {
            placeholder.setMethod(res);
        }

        return res;
    }

    public SymbolReference<ResolvedTypeDeclaration> solve(ThisExpr node) {
        // If 'this' is prefixed by a class eg. MyClass.this
        if (node.getTypeName().isPresent()) {
            // Get the class name
            String className = node.getTypeName().get().asString();
            // Attempt to resolve using a typeSolver
            SymbolReference<ResolvedReferenceTypeDeclaration> clazz = typeSolver.tryToSolveType(className);
            if (clazz.isSolved()) {
                return solved(clazz.getCorrespondingDeclaration());
            }
            // Attempt to resolve locally in Compilation unit
            Optional<CompilationUnit> cu = node.findAncestor(CompilationUnit.class);
            if (cu.isPresent()) {
                Optional<ClassOrInterfaceDeclaration> classByName = cu.get().getClassByName(className);
                if (classByName.isPresent()) {
                    return solved(getTypeDeclaration(classByName.get()));
                }
            }
        }
        return solved(getTypeDeclaration(findContainingTypeDeclOrObjectCreationExpr(node)));
    }

    /**
     * Given a constructor call find out to which constructor declaration it corresponds.
     */
    public SymbolReference<ResolvedConstructorDeclaration> solve(
            ObjectCreationExpr objectCreationExpr, boolean solveLambdas) {
        List<ResolvedType> argumentTypes = new LinkedList<>();
        List<LambdaArgumentTypePlaceholder> placeholders = new LinkedList<>();

        solveArguments(
                objectCreationExpr, objectCreationExpr.getArguments(), solveLambdas, argumentTypes, placeholders);

        ResolvedReferenceTypeDeclaration typeDecl = null;
        if (objectCreationExpr.getAnonymousClassBody().isPresent()) {
            typeDecl = new JavaParserAnonymousClassDeclaration(objectCreationExpr, typeSolver);
        } else {
            ResolvedType classDecl =
                    JavaParserFacade.get(typeSolver).convert(objectCreationExpr.getType(), objectCreationExpr);
            if (classDecl.isReferenceType()
                    && classDecl.asReferenceType().getTypeDeclaration().isPresent()) {
                typeDecl = classDecl.asReferenceType().getTypeDeclaration().get();
            }
        }
        if (typeDecl == null) {
            return unsolved();
        }
        SymbolReference<ResolvedConstructorDeclaration> res =
                ConstructorResolutionLogic.findMostApplicable(typeDecl.getConstructors(), argumentTypes, typeSolver);
        for (LambdaArgumentTypePlaceholder placeholder : placeholders) {
            placeholder.setMethod(res);
        }
        return res;
    }

    private void solveArguments(
            Node node,
            NodeList<Expression> args,
            boolean solveLambdas,
            List<ResolvedType> argumentTypes,
            List<LambdaArgumentTypePlaceholder> placeholders) {
        int i = 0;
        for (Expression parameterValue : args) {
            while (parameterValue instanceof EnclosedExpr) {
                parameterValue = ((EnclosedExpr) parameterValue).getInner();
            }
            // In order to resolve a call with a lambda expr as an argument, the functional interface implemented
            // by that lambda must be determined. This is done by collecting the candidate functional methods in
            // scope and then excluding non-applicable methods if any of the following hold:
            //   1. The lambda and the candidate method do not have the same number of arguments/parameters
            //   2. The lambda has an explicit empty/void return statement `return;` in the body block, but the
            //      candidate method has a non-void return type.
            //   3. The lambda has an explicit non-void return statement, e.g. `return x;`, but the candidate
            //      method has a void return type.
            // For JavaParser to be able to perform the same filtering, we need to keep track of the number of
            // arguments to the lambda, as well as whether there is an explicit void/non-void return statement,
            // so this information is added to the `LambdaArgumentTypePlaceholder` in the block below.
            if (parameterValue.isLambdaExpr()) {
                LambdaExpr lambdaExpr = parameterValue.asLambdaExpr();
                Optional<Boolean> bodyBlockHasExplicitNonVoidReturn;
                if (!lambdaExpr.getBody().isBlockStmt()) {
                    bodyBlockHasExplicitNonVoidReturn = Optional.empty();
                } else {
                    Optional<ReturnStmt> explicitReturn = lambdaExpr.getBody().findFirst(ReturnStmt.class);
                    if (explicitReturn.isPresent()) {
                        bodyBlockHasExplicitNonVoidReturn =
                                Optional.of(explicitReturn.get().getExpression().isPresent());
                    } else {
                        bodyBlockHasExplicitNonVoidReturn = Optional.of(false);
                    }
                }
                LambdaArgumentTypePlaceholder placeholder = new LambdaArgumentTypePlaceholder(
                        i, lambdaExpr.getParameters().size(), bodyBlockHasExplicitNonVoidReturn);
                argumentTypes.add(placeholder);
                placeholders.add(placeholder);
            } else if (parameterValue.isMethodReferenceExpr()) {
                LambdaArgumentTypePlaceholder placeholder = new LambdaArgumentTypePlaceholder(i);
                argumentTypes.add(placeholder);
                placeholders.add(placeholder);
            } else {
                try {
                    argumentTypes.add(JavaParserFacade.get(typeSolver).getType(parameterValue, solveLambdas));
                } catch (Exception e) {
                    throw failureHandler.handle(
                            e,
                            String.format(
                                    "Unable to calculate the type of a parameter of a method call. Method call: %s, Parameter: %s",
                                    node, parameterValue));
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

        SymbolReference<ResolvedMethodDeclaration> res = JavaParserFactory.getContext(methodCallExpr, typeSolver)
                .solveMethod(methodCallExpr.getName().getId(), argumentTypes, false);
        for (LambdaArgumentTypePlaceholder placeholder : placeholders) {
            placeholder.setMethod(res);
        }
        return res;
    }

    /**
     * Given a method reference find out to which method declaration it corresponds.
     */
    public SymbolReference<ResolvedMethodDeclaration> solve(
            MethodReferenceExpr methodReferenceExpr, boolean solveLambdas) {
        // pass empty argument list to be populated
        List<ResolvedType> argumentTypes = new LinkedList<>();
        return JavaParserFactory.getContext(methodReferenceExpr, typeSolver)
                .solveMethod(methodReferenceExpr.getIdentifier(), argumentTypes, false);
    }

    public SymbolReference<ResolvedAnnotationDeclaration> solve(AnnotationExpr annotationExpr) {
        Context context = JavaParserFactory.getContext(annotationExpr, typeSolver);
        SymbolReference<ResolvedTypeDeclaration> typeDeclarationSymbolReference =
                context.solveType(annotationExpr.getNameAsString());
        if (typeDeclarationSymbolReference.isSolved()) {
            ResolvedAnnotationDeclaration annotationDeclaration =
                    (ResolvedAnnotationDeclaration) typeDeclarationSymbolReference.getCorrespondingDeclaration();
            return solved(annotationDeclaration);
        }
        return unsolved();
    }

    public SymbolReference<ResolvedValueDeclaration> solve(FieldAccessExpr fieldAccessExpr) {
        return ((FieldAccessContext) JavaParserFactory.getContext(fieldAccessExpr, typeSolver))
                .solveField(fieldAccessExpr.getName().getId());
    }

    /**
     * Get the type associated with the node.
     * <p>
     * This method was originally intended to get the type of a value: any value has a type.
     * <p>
     * For example:
     * <pre>
     * int foo(int a) {
     *     return a; // when getType is invoked on "a" it returns the type "int"
     * }
     * </pre>
     * <p>
     * Now, users started using also of names of types itself, which do not have a type.
     * <p>
     * For example:
     * <pre>
     * class A {
     *     int foo(int a) {
     *         return A.someStaticField; // when getType is invoked on "A", which represents a class, it returns
     *             // the type "A" itself while it used to throw UnsolvedSymbolException
     * }
     * </pre>
     * <p>
     * To accommodate this usage and avoid confusion this method return
     * the type itself when used on the name of type.
     */
    public ResolvedType getType(Node node) {
        try {
            return getType(node, true);
        } catch (UnsolvedSymbolException e) {
            if (node instanceof NameExpr) {
                NameExpr nameExpr = (NameExpr) node;
                SymbolReference<ResolvedTypeDeclaration> typeDeclaration =
                        JavaParserFactory.getContext(node, typeSolver).solveType(nameExpr.getNameAsString());
                if (typeDeclaration.isSolved()
                        && typeDeclaration.getCorrespondingDeclaration() instanceof ResolvedReferenceTypeDeclaration) {
                    ResolvedReferenceTypeDeclaration resolvedReferenceTypeDeclaration =
                            (ResolvedReferenceTypeDeclaration) typeDeclaration.getCorrespondingDeclaration();
                    return ReferenceTypeImpl.undeterminedParameters(resolvedReferenceTypeDeclaration);
                }
            }
            throw failureHandler.handle(e);
        }
    }

    /*
     * Returns the resolved Type of the {@code Node}. If the node is a method call
     * expression and the flag activates lambda expression resolution, the type
     * of the arguments to the expression are looked up beforehand so that the type
     * resolution is as relevant as possible.
     */
    public ResolvedType getType(Node node, boolean solveLambdas) {
        if (solveLambdas) {
            if (!node.containsData(TYPE_WITH_LAMBDAS_RESOLVED)) {

                if (node instanceof MethodCallExpr) {
                    MethodCallExpr methodCallExpr = (MethodCallExpr) node;
                    for (Node arg : methodCallExpr.getArguments()) {
                        if (!arg.containsData(TYPE_WITH_LAMBDAS_RESOLVED)) {
                            getType(arg, true);
                        }
                    }
                }
                ResolvedType res = getTypeConcrete(node, solveLambdas);
                if (res == null) {
                    throw new IllegalStateException("Resolved type is null for node: " + node);
                }
                node.setData(TYPE_WITH_LAMBDAS_RESOLVED, res);
                Log.trace("getType on %s  -> %s", () -> node, () -> res);
            }
            return node.getData(TYPE_WITH_LAMBDAS_RESOLVED);
        }

        // Try to return a value from the cache of resolved types using lambda expressions
        Optional<ResolvedType> res = node.findData(TYPE_WITH_LAMBDAS_RESOLVED);
        if (res.isPresent()) {
            return res.get();
        }

        // else try to return a value from the cache of resolved types without lambda expressions
        // Or resolves the node type without resolving the lambda expressions
        return node.findData(TYPE_WITHOUT_LAMBDAS_RESOLVED).orElseGet(() -> {
            ResolvedType resType = getTypeConcrete(node, solveLambdas);
            node.setData(TYPE_WITHOUT_LAMBDAS_RESOLVED, resType);
            Log.trace("getType on %s (no solveLambdas) -> %s", () -> node, () -> res);
            return resType;
        });
    }

    protected MethodUsage toMethodUsage(MethodReferenceExpr methodReferenceExpr, List<ResolvedType> paramTypes) {
        // JLS §15.13.1: "A method reference expression consists of a ReferenceType or Primary,
        // followed by :: and a method name."
        // We need to evaluate the scope to determine what we're referencing.
        Expression scope = methodReferenceExpr.getScope();
        ResolvedType typeOfScope = getType(scope);

        // JLS §15.13.1: The scope must be a reference type
        if (!typeOfScope.isReferenceType()) {
            throw new UnsupportedOperationException("Cannot resolve method reference on non-reference type: "
                    + typeOfScope.getClass().getCanonicalName());
        }

        // Extract the type declaration from the reference type
        ResolvedReferenceTypeDeclaration resolvedTypeDecl = typeOfScope
                .asReferenceType()
                .getTypeDeclaration()
                .orElseThrow(() ->
                        new UnsolvedSymbolException("TypeDeclaration unexpectedly empty for type: " + typeOfScope));

        Set<MethodUsage> allMethods = resolvedTypeDecl.getAllMethods();
        String methodName = methodReferenceExpr.getIdentifier();

        // JLS §15.12.2.1: "Identify Potentially Applicable Methods"
        // "The class or interface determined by compile-time step 1 (§15.12.1) is searched
        // for all member methods that are potentially applicable to this method invocation."
        // Filter methods by name first.
        List<MethodUsage> candidateMethods =
                allMethods.stream().filter(m -> m.getName().equals(methodName)).collect(Collectors.toList());

        if (candidateMethods.isEmpty()) {
            throw new UnsolvedSymbolException("Cannot find method '" + methodName + "' in type " + typeOfScope);
        }

        // JLS §15.13.1: Method references have different forms based on their scope:
        //
        // Form 1: ReferenceType :: [TypeArguments] Identifier
        //   Example: String::length, Integer::parseInt
        //   Two possible interpretations:
        //   a) Static method: All function type parameters map to method parameters
        //      Example: Integer::parseInt with Function<String,Integer>
        //               → parseInt(String) is static, paramTypes = [String]
        //               → ALL paramTypes go to method parameters: [String]
        //
        //   b) Unbound instance method: First function type parameter is the receiver type
        //      Example: String::length with Function<String,Integer>
        //               → length() is instance, paramTypes = [String] where String is receiver
        //               → ONLY remaining paramTypes go to method parameters: []
        //
        // Form 2: Primary :: [TypeArguments] Identifier
        //   Example: foo::convert where foo is an expression
        //   Only instance methods (bound to the Primary expression result)
        //   ALL function type parameters map to method parameters
        //   Example: foo::convert with Function<Integer,String>
        //            → convert(int) is instance, paramTypes = [Integer]
        //            → ALL paramTypes go to method parameters: [Integer]
        //            → The receiver is foo (already bound at reference creation time)
        Optional<MethodUsage> result;

        if (scope.isTypeExpr() && typeOfScope.isReferenceType() && !methodReferenceExpr.isScopePrimaryExpr()) {
            // JLS §15.13.1: "If the method reference expression has the form ReferenceType ::
            // [TypeArguments] Identifier, the potentially applicable methods are:"
            //
            // This is FORM 1: The scope is a type name (e.g., String, Integer, Foo)
            //
            // Two distinct cases must be tried:
            // Case 1a: Static method - all paramTypes are method parameters
            // Case 1b: Unbound instance method - first paramType is receiver, rest are method parameters

            // CASE 1a: Try static methods first
            // JLS §15.13.1: For static methods, "the arity of m is k, and the type of each
            // parameter matches the corresponding parameter type of the function type"
            // This means: ALL paramTypes map to method parameters
            List<MethodUsage> staticMethods = candidateMethods.stream()
                    .filter(m -> m.getDeclaration().isStatic())
                    .collect(Collectors.toList());

            if (!staticMethods.isEmpty()) {
                // JLS §15.12.2: Apply the method resolution process (phases 1-3)
                // Pass ALL paramTypes because they all map to method parameters
                result = MethodResolutionLogic.findMostApplicableUsage(
                        staticMethods, methodName, paramTypes, typeSolver);

                if (result.isPresent()) {
                    return result.get();
                }
            }

            // CASE 1b: Try unbound instance methods
            // JLS §15.13.1: For unbound instance methods with ReferenceType scope:
            // "The arity of m is n, where m has n formal parameters and the function type has n+1 parameter types"
            // This means: First paramType is the receiver type, remaining paramTypes are method parameters
            if (!paramTypes.isEmpty()) {
                List<MethodUsage> instanceMethods = candidateMethods.stream()
                        .filter(m -> !m.getDeclaration().isStatic())
                        .collect(Collectors.toList());

                if (!instanceMethods.isEmpty()) {
                    // Split paramTypes: first is receiver, rest are method parameters
                    // Example: Function<String, Integer> has paramTypes = [String, Integer]
                    //          For String::concat, first param (String) is receiver
                    //          Remaining params ([Integer]) go to method parameters
                    List<ResolvedType> methodParams = paramTypes.subList(1, paramTypes.size());

                    // JLS §15.12.2.2-4: Apply phases 1-3 of method resolution
                    // Pass only the method parameters (excluding receiver type)
                    result = MethodResolutionLogic.findMostApplicableUsage(
                            instanceMethods, methodName, methodParams, typeSolver);

                    if (result.isPresent()) {
                        return result.get();
                    }
                }
            }
        } else {
            // JLS §15.13.1: "If the method reference expression has the form
            // Primary :: [TypeArguments] Identifier"
            //
            // This is FORM 2: The scope is an expression (e.g., foo, myString, System.out)
            //
            // CRITICAL: In this form, the expression is evaluated and becomes the BOUND RECEIVER
            // at method reference creation time, not at invocation time.
            //
            // "The potentially applicable methods are the member methods of the type
            // of the Primary that are not static"
            //
            // For bound instance methods: ALL functional interface parameters map to method parameters
            // The receiver is NOT part of paramTypes - it's already bound to the expression result
            //
            // Example from failing test:
            //   Foo foo = new Foo();
            //   Optional<Integer> priority = Optional.of(4);
            //   priority.map(foo::convert).orElse("0");
            //
            // Analysis:
            //   - scope = foo (a Primary expression, not a type)
            //   - foo is evaluated → becomes bound receiver
            //   - map() expects Function<Integer, String>
            //   - paramTypes = [Integer] (from Function's parameter type)
            //   - convert(int) signature: takes 1 parameter
            //   - ALL paramTypes [Integer] go to method parameters
            //   - Match: convert(int) with [Integer] ✓
            List<MethodUsage> instanceMethods = candidateMethods.stream()
                    .filter(m -> !m.getDeclaration().isStatic())
                    .collect(Collectors.toList());

            if (instanceMethods.isEmpty()) {
                throw new UnsolvedSymbolException("No non-static methods named '" + methodName + "' found in type "
                        + typeOfScope + " (method reference with expression scope must reference instance methods)");
            }

            // JLS §15.12.2.2-4: Apply the three-phase method resolution
            // IMPORTANT: Pass ALL paramTypes - they ALL go to method parameters
            // The receiver (foo) is already bound and is NOT part of paramTypes
            result = MethodResolutionLogic.findMostApplicableUsage(instanceMethods, methodName, paramTypes, typeSolver);

            if (result.isPresent()) {
                return result.get();
            }
        }

        // JLS §15.12.2.5: "Choosing the Most Specific Method"
        // If we cannot find a most specific method, the reference is ambiguous or no applicable method exists
        throw new UnsupportedOperationException(
                "Unable to resolve method reference " + methodReferenceExpr + " with param types "
                        + paramTypes + ". Candidates found: "
                        + candidateMethods.size() + " method(s) named '"
                        + methodName + "' in type " + typeOfScope);
    }

    protected ResolvedType getBinaryTypeConcrete(
            Node left, Node right, boolean solveLambdas, BinaryExpr.Operator operator) {
        ResolvedType leftType = getTypeConcrete(left, solveLambdas);
        ResolvedType rightType = getTypeConcrete(right, solveLambdas);

        // JLS 15.18.1. String Concatenation Operator +
        // If only one operand expression is of type String, then string conversion (§5.1.11) is performed on the other
        // operand to produce a string at run time.
        //
        // The result of string concatenation is a reference to a String object that is the concatenation of the two
        // operand strings. The characters of the left-hand operand precede the characters of the right-hand operand in
        // the newly created string.

        if (operator == BinaryExpr.Operator.PLUS) {
            boolean isLeftString = leftType.isReferenceType()
                    && leftType.asReferenceType().getQualifiedName().equals(JAVA_LANG_STRING);
            boolean isRightString = rightType.isReferenceType()
                    && rightType.asReferenceType().getQualifiedName().equals(JAVA_LANG_STRING);
            if (isLeftString || isRightString) {
                return isLeftString ? leftType : rightType;
            }
        }

        // JLS 5.6.2. Binary Numeric Promotion
        //
        // Widening primitive conversion (§5.1.2) is applied to convert either or both operands as specified by the
        // following rules:
        //
        // * If either operand is of type double, the other is converted to double.
        // * Otherwise, if either operand is of type float, the other is converted to float.
        // * Otherwise, if either operand is of type long, the other is converted to long.
        // * Otherwise, both operands are converted to type int.

        boolean isLeftNumeric = leftType.isPrimitive() && leftType.asPrimitive().isNumeric();
        boolean isRightNumeric =
                rightType.isPrimitive() && rightType.asPrimitive().isNumeric();

        if (isLeftNumeric && isRightNumeric) {
            return leftType.asPrimitive().bnp(rightType.asPrimitive());
        }

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

    /**
     * Where a node has an interface/class/enum declaration as its ancestor, return the nearest one.
     * <p>
     * NOTE: See {@link #findContainingTypeDeclOrObjectCreationExpr} if wanting to include anonymous inner classes.
     * <p>
     * For example, these all return X:
     * {@code public interface X { ... node here ... }}
     * {@code public class X { ... node here ... }}
     * {@code public enum X { ... node here ... }}
     *
     * @param node The Node whose ancestors will be traversed,
     * @return The first class/interface/enum declaration in the Node's ancestry.
     */
    protected TypeDeclaration<?> findContainingTypeDecl(Node node) {
        Node parent = node;
        while (true) {
            parent = demandParentNode(parent);
            if (parent instanceof TypeDeclaration) {
                return (TypeDeclaration<?>) parent;
            }
        }
    }

    /**
     * Where a node has an interface/class/enum declaration -- or an object creation expression (anonymous inner class)
     * -- as its ancestor, return the nearest one.
     * <p>
     * NOTE: See {@link #findContainingTypeDecl} if wanting to not include anonymous inner classes.
     * <p>
     * For example, these all return X:
     * <ul>
     *     <li>{@code public interface X { ... node here ... }}</li>
     *     <li>{@code public class X { ... node here ... }}</li>
     *     <li>{@code public enum X { ... node here ... }}</li>
     *     <li><pre>{@code
     *     new ActionListener() {
     *          ... node here ...
     *          public void actionPerformed(ActionEvent e) {
     *               ... or node here ...
     *          }
     *     }
     *     }</pre></li>
     * </ul>
     * <p>
     *
     * @param node The Node whose ancestors will be traversed,
     * @return The first class/interface/enum declaration -- or object creation expression (anonymous inner class) -- in
     * the Node's ancestry.
     */
    protected Node findContainingTypeDeclOrObjectCreationExpr(Node node) {
        Node parent = node;
        boolean detachFlag = false;
        while (true) {
            parent = demandParentNode(parent);
            if (parent instanceof BodyDeclaration) {
                if (parent instanceof TypeDeclaration) {
                    return parent;
                }
                detachFlag = true;
            }
            if (parent instanceof ObjectCreationExpr) {
                if (detachFlag) {
                    return parent;
                }
            }
        }
    }

    /**
     * Where a node has an interface/class/enum declaration -- or an object creation expression in an inner class
     * references an outer class -- as its ancestor, return the declaration corresponding to the class name specified.
     */
    protected Node findContainingTypeDeclOrObjectCreationExpr(Node node, String className) {
        Node parent = node;
        boolean detachFlag = false;
        while (true) {
            parent = demandParentNode(parent);
            if (parent instanceof BodyDeclaration) {
                if (parent instanceof TypeDeclaration
                        && ((TypeDeclaration<?>) parent)
                                .getFullyQualifiedName()
                                .orElse("")
                                .endsWith(className)) {
                    return parent;
                }
                detachFlag = true;
            }
            if (parent instanceof ObjectCreationExpr
                    && ((ObjectCreationExpr) parent)
                            .getType()
                            .getName()
                            .asString()
                            .equals(className)) {
                if (detachFlag) {
                    return parent;
                }
            }
        }
    }

    /**
     * Convert a {@link Type} into the corresponding {@link ResolvedType}.
     *
     * @param type      The type to be converted.
     * @param context   The current context.
     *
     * @return The type resolved.
     */
    protected ResolvedType convertToUsage(Type type, Context context) {
        if (context == null) {
            throw new NullPointerException("Context should not be null");
        }
        return type.convertToUsage(context);
    }

    /**
     * Convert a {@link Type} into the corresponding {@link ResolvedType}.
     *
     * @param type The type to be converted.
     *
     * @return The type resolved.
     */
    public ResolvedType convertToUsage(Type type) {
        return convertToUsage(type, JavaParserFactory.getContext(type, typeSolver));
    }

    private Optional<ForEachStmt> forEachStmtWithVariableDeclarator(VariableDeclarator variableDeclarator) {
        Optional<Node> node = variableDeclarator.getParentNode();
        if (!node.isPresent() || !(node.get() instanceof VariableDeclarationExpr)) {
            return Optional.empty();
        }
        node = node.get().getParentNode();
        if (!node.isPresent() || !(node.get() instanceof ForEachStmt)) {
            return Optional.empty();
        }
        return Optional.of((ForEachStmt) node.get());
    }

    public ResolvedType convert(Type type, Node node) {
        return convert(type, JavaParserFactory.getContext(node, typeSolver));
    }

    public ResolvedType convert(Type type, Context context) {
        return convertToUsage(type, context);
    }

    public MethodUsage solveMethodAsUsage(MethodCallExpr call) {
        List<ResolvedType> params = new ArrayList<>();
        if (call.getArguments() != null) {
            for (Expression param : call.getArguments()) {
                // getTypeConcrete(Node node, boolean solveLambdas)
                try {
                    params.add(getType(param, false));
                } catch (Exception e) {
                    throw failureHandler.handle(
                            e,
                            String.format("Error calculating the type of parameter %s of method call %s", param, call));
                }
                // params.add(getTypeConcrete(param, false));
            }
        }
        Context context = JavaParserFactory.getContext(call, typeSolver);
        Optional<MethodUsage> methodUsage =
                context.solveMethodAsUsage(call.getName().getId(), params);
        if (!methodUsage.isPresent()) {
            throw new UnsolvedSymbolException("Method '" + call.getName() + "' cannot be resolved in context " + call
                    + " (line: " + call.getRange().map(r -> "" + r.begin.line).orElse("??") + ") " + context
                    + ". Parameter types: " + params);
        }
        return methodUsage.get();
    }

    public ResolvedReferenceTypeDeclaration getTypeDeclaration(Node node) {
        if (node instanceof TypeDeclaration) {
            return getTypeDeclaration((TypeDeclaration) node);
        }
        if (node instanceof ObjectCreationExpr) {
            return new JavaParserAnonymousClassDeclaration((ObjectCreationExpr) node, typeSolver);
        }
        throw new IllegalArgumentException();
    }

    public ResolvedReferenceTypeDeclaration getTypeDeclaration(
            ClassOrInterfaceDeclaration classOrInterfaceDeclaration) {
        return symbolResolver.toTypeDeclaration(classOrInterfaceDeclaration);
    }

    /**
     * "this" inserted in the given point, which type would have?
     */
    public ResolvedType getTypeOfThisIn(Node node) {
        // TODO consider static methods
        if (node instanceof ClassOrInterfaceDeclaration) {
            return new ReferenceTypeImpl(getTypeDeclaration((ClassOrInterfaceDeclaration) node));
        }
        if (node instanceof RecordDeclaration) {
            return new ReferenceTypeImpl(getTypeDeclaration((RecordDeclaration) node));
        }
        if (node instanceof EnumDeclaration) {
            JavaParserEnumDeclaration enumDeclaration =
                    new JavaParserEnumDeclaration((EnumDeclaration) node, typeSolver);
            return new ReferenceTypeImpl(enumDeclaration);
        }
        if (node instanceof ObjectCreationExpr
                && ((ObjectCreationExpr) node).getAnonymousClassBody().isPresent()) {
            JavaParserAnonymousClassDeclaration anonymousDeclaration =
                    new JavaParserAnonymousClassDeclaration((ObjectCreationExpr) node, typeSolver);
            return new ReferenceTypeImpl(anonymousDeclaration);
        }
        return getTypeOfThisIn(demandParentNode(node));
    }

    public ResolvedReferenceTypeDeclaration getTypeDeclaration(TypeDeclaration<?> typeDeclaration) {
        return symbolResolver.toTypeDeclaration(typeDeclaration);
    }

    /**
     * Convert a {@link Class} into the corresponding {@link ResolvedType}.
     *
     * @param clazz The class to be converted.
     *
     * @return The class resolved.
     *
     * @deprecated instead consider SymbolSolver.classToResolvedType(Class<?> clazz)
     */
    @Deprecated
    public ResolvedType classToResolvedType(Class<?> clazz) {
        Solver symbolSolver = new SymbolSolver(new ReflectionTypeSolver());
        return symbolSolver.classToResolvedType(clazz);
    }
}
