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

package com.github.javaparser.symbolsolver.resolution.javaparser.contexts;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.Context;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.Navigator;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.resolution.types.ResolvedVoidType;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.MethodCallExprContext;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ClassLoaderTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.github.javaparser.symbolsolver.utils.LeanParserConfiguration;
import java.net.URL;
import java.net.URLClassLoader;
import java.nio.file.Path;
import java.util.*;
import java.util.stream.Collectors;
import org.junit.jupiter.api.Test;

/**
 * @author Malte Langkabel
 */
class MethodCallExprContextResolutionTest extends AbstractResolutionTest {
    private MethodCallExpr getMethodCallExpr(String methodName, String callingMethodName) {
        CompilationUnit cu = parseSample("MethodCalls");

        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "MethodCalls");
        MethodDeclaration method = Navigator.demandMethod(clazz, methodName);
        return Navigator.findMethodCall(method, callingMethodName).get();
    }

    private CombinedTypeSolver createTypeSolver() {
        Path src = adaptPath("src/test/resources");
        CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver();
        combinedTypeSolver.add(new ReflectionTypeSolver());
        combinedTypeSolver.add(new JavaParserTypeSolver(src, new LeanParserConfiguration()));
        return combinedTypeSolver;
    }

    @Test
    void solveNestedMethodCallExprContextWithoutScope() {
        MethodCallExpr methodCallExpr = getMethodCallExpr("bar1", "foo");
        CombinedTypeSolver typeSolver = createTypeSolver();

        Context context = new MethodCallExprContext(methodCallExpr, typeSolver);

        Optional<MethodUsage> ref = context.solveMethodAsUsage("foo", Collections.emptyList());
        assertTrue(ref.isPresent());
        assertEquals("MethodCalls", ref.get().declaringType().getQualifiedName());
    }

    @Test
    void solveGenericMethodCallMustUseProvidedTypeArgs() {
        assertCanSolveGenericMethodCallMustUseProvidedTypeArgs("genericMethod0");
    }

    @Test
    void solveStaticGenericMethodCallMustUseProvidedTypeArgs() {
        assertCanSolveGenericMethodCallMustUseProvidedTypeArgs("staticGenericMethod0");
    }

    private void assertCanSolveGenericMethodCallMustUseProvidedTypeArgs(String callMethodName) {
        MethodCallExpr methodCallExpr = getMethodCallExpr("genericMethodTest", callMethodName);
        CombinedTypeSolver typeSolver = createTypeSolver();

        MethodCallExprContext context = new MethodCallExprContext(methodCallExpr, typeSolver);

        Optional<MethodUsage> ref = context.solveMethodAsUsage(callMethodName, Collections.emptyList());
        assertTrue(ref.isPresent());
        assertEquals("MethodCalls", ref.get().declaringType().getQualifiedName());
        assertEquals(
                Collections.singletonList("java.lang.Integer"),
                ref.get().typeParametersMap().getTypes().stream()
                        .map(ty -> ty.asReferenceType().describe())
                        .collect(Collectors.toList()));
    }

    @Test
    void solveGenericMethodCallCanInferFromArguments() {
        assertCanSolveGenericMethodCallCanInferFromArguments("genericMethod1");
    }

    @Test
    void solveStaticGenericMethodCallCanInferFromArguments() {
        assertCanSolveGenericMethodCallCanInferFromArguments("staticGenericMethod1");
    }

    private void assertCanSolveGenericMethodCallCanInferFromArguments(String callMethodName) {
        MethodCallExpr methodCallExpr = getMethodCallExpr("genericMethodTest", callMethodName);
        CombinedTypeSolver typeSolver = createTypeSolver();

        MethodCallExprContext context = new MethodCallExprContext(methodCallExpr, typeSolver);

        ResolvedReferenceTypeDeclaration stringType = typeSolver.solveType("java.lang.String");

        List<ResolvedType> argumentsTypes = new ArrayList<>();
        argumentsTypes.add(new ReferenceTypeImpl(stringType));

        Optional<MethodUsage> ref = context.solveMethodAsUsage(callMethodName, argumentsTypes);
        assertTrue(ref.isPresent());
        assertEquals("MethodCalls", ref.get().declaringType().getQualifiedName());
        assertEquals(
                Collections.singletonList("java.lang.String"),
                ref.get().typeParametersMap().getTypes().stream()
                        .map(ty -> ty.asReferenceType().describe())
                        .collect(Collectors.toList()));
    }

    @Test
    public void test() {
        ParserConfiguration config =
                new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(createTypeSolver()));
        StaticJavaParser.setConfiguration(config);
        CompilationUnit cu = parseSample("Issue2258");
        List<MethodCallExpr> expressions = cu.getChildNodesByType(MethodCallExpr.class);
        assertEquals(2, expressions.size());
        ResolvedType r = expressions.get(1).calculateResolvedType();
        assertTrue(ResolvedVoidType.class.isAssignableFrom(r.getClass()));
    }

    @Test
    public void testGenericParameter() {
        ParserConfiguration config =
                new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(createTypeSolver()));
        StaticJavaParser.setConfiguration(config);
        CompilationUnit cu = parseSample("ISSUES_Generic_Parameter");
        List<MethodCallExpr> expressions = cu.getChildNodesByType(MethodCallExpr.class);
        assertEquals(1, expressions.size());
        ResolvedType r = expressions.get(0).calculateResolvedType();
        assertTrue(ReferenceTypeImpl.class.isAssignableFrom(r.getClass()));
    }

    @Test
    public void testResolveChainedCallOnReflectionType() throws Exception {
        Path pathToJar = adaptPath("src/test/resources/issue2667/jsonobject.jar");

        CombinedTypeSolver typeSolver = createTypeSolver();
        typeSolver.add(new ClassLoaderTypeSolver(
                new URLClassLoader(new URL[] {pathToJar.toUri().toURL()})));

        ParserConfiguration config = new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(typeSolver));
        StaticJavaParser.setConfiguration(config);
        CompilationUnit cu = parseSample("Issue2667");
        Set<MethodCallExpr> methodCallExpr = new HashSet<>(cu.findAll(MethodCallExpr.class));

        int errorCount = 0;

        for (MethodCallExpr expr : methodCallExpr) {
            try {
                ResolvedMethodDeclaration rd = expr.resolve();
            } catch (UnsolvedSymbolException e) {
                errorCount++;
            }
        }

        assertEquals(0, errorCount, "Expected zero UnsolvedSymbolException s");
    }

    @Test
    void solveVariadicStaticGenericMethodCallCanInferFromArguments() {
        ParserConfiguration config =
                new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(createTypeSolver()));
        StaticJavaParser.setConfiguration(config);
        MethodCallExpr methodCallExpr = getMethodCallExpr("genericMethodTest", "variadicStaticGenericMethod");

        ResolvedType resolvedType = methodCallExpr.calculateResolvedType();
        assertEquals("java.lang.String", resolvedType.describe());
    }

    // Related to issue #3751
    /**
     * Verifies that {@code calculateResolvedType()} resolves the return type of
     * {@code stream.collect(Collectors.toList())} without throwing an exception (issue #3751).
     *
     * <p>{@code Collectors.toList()} returns {@code Collector<T, ?, List<T>>}: the intermediate
     * accumulation type is the unbounded wildcard {@code ?}.  {@code Stream.collect} is declared as
     * {@code <R, A> R collect(Collector<? super T, A, R>)}, so resolving the return type requires
     * matching the formal type variable {@code A} against the wildcard {@code ?}.
     *
     * <p>Before the fix, {@code matchTypeParameters} threw {@code UnsupportedOperationException}
     * in this situation because it only accepted type variables, reference types, and arrays as
     * candidates for type-variable bindings — wildcards were not handled.  The fix applies
     * capture-conversion rules: bounded wildcards contribute their declared bound, and unbounded
     * wildcards are skipped (no type information can be inferred from {@code ?} alone).  This
     * leaves {@code A} unresolved while still allowing {@code R = List<String>} to be inferred
     * correctly from the remaining type arguments.
     */
    @Test
    void resolveStreamCollectWithWildcardAccumulatorType() {
        ParserConfiguration config =
                new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));
        StaticJavaParser.setConfiguration(config);
        CompilationUnit cu = parseSample("Issue3751");
        List<MethodCallExpr> expressions = cu.getChildNodesByType(MethodCallExpr.class);

        MethodCallExpr collectCall = expressions.stream()
                .filter(e -> e.getNameAsString().equals("collect"))
                .findFirst()
                .orElseThrow(() -> new AssertionError("No 'collect' call found in Issue3751 sample"));

        // Must not throw UnsupportedOperationException (issue #3751)
        ResolvedType resolvedType = collectCall.calculateResolvedType();
        assertEquals("java.util.List<java.lang.String>", resolvedType.describe());
    }

    /**
     * Verifies that the wildcard fix does not regress the common case where all type arguments are
     * concrete (no wildcards involved).  {@code Stream.collect(Collectors.toList())} returns
     * {@code List<String>} which must still resolve correctly.
     */
    @Test
    void resolveStreamCollectWithConcreteCollector() {
        ParserConfiguration config =
                new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));
        StaticJavaParser.setConfiguration(config);

        String code = "import java.util.*; import java.util.stream.*;"
                + "class T { List<String> f(Stream<String> s) { return s.collect(Collectors.toList()); } }";
        CompilationUnit cu = StaticJavaParser.parse(code);

        MethodCallExpr collectCall = cu.getChildNodesByType(MethodCallExpr.class).stream()
                .filter(e -> e.getNameAsString().equals("collect"))
                .findFirst()
                .orElseThrow(() -> new AssertionError("No 'collect' call found"));

        ResolvedType resolvedType = collectCall.calculateResolvedType();
        assertEquals("java.util.List<java.lang.String>", resolvedType.describe());
    }

    /**
     * Verifies the original case from issue #3751: resolving
     * {@code stream.collect(Collectors.groupingBy(String::new, Collectors.counting()))} must not
     * throw and must produce a {@code Map<?, Long>} return type.
     *
     * <p>Two fixes cooperate here:
     * <ol>
     *   <li>The wildcard fix in {@code matchTypeParameters} – prevents
     *       {@code UnsupportedOperationException} when matching the formal type variable {@code A}
     *       against the wildcard {@code ?} in {@code Collector<T, ?, R>}.</li>
     *   <li>The constructor-reference fix in {@code TypeExtractor} – {@code String::new} now
     *       resolves to the functional interface type expected at its call-site position
     *       ({@code Function<? super T, ? extends K>}) so that the correct {@code groupingBy}
     *       overload can be found instead of throwing {@code UnsolvedSymbolException}.</li>
     * </ol>
     *
     * <p><b>Note on partial resolution:</b> the key type variable {@code K} (the grouping key)
     * resolves to {@code String} in a real Java compiler through two-phase poly-expression
     * inference (JLS §15.12.2.7).  JavaParser's symbol solver does not yet implement that
     * multi-pass inference, so {@code K} may appear as an unresolved inference variable in the
     * output.  The assertions below therefore check the outer container type ({@code Map}) and
     * the value type ({@code Long}) without pinning the exact key type.
     */
    @Test
    void resolveStreamCollectGroupingByWithConstructorReference() {
        ParserConfiguration config =
                new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));
        StaticJavaParser.setConfiguration(config);
        CompilationUnit cu = parseSample("Issue3751");
        List<MethodCallExpr> expressions = cu.getChildNodesByType(MethodCallExpr.class);

        // The sample contains two collect() calls; pick the one inside groupAndCount().
        MethodCallExpr collectCall = expressions.stream()
                .filter(e -> e.getNameAsString().equals("collect"))
                .filter(e -> e.findAncestor(com.github.javaparser.ast.body.MethodDeclaration.class)
                        .map(m -> m.getNameAsString().equals("groupAndCount"))
                        .orElse(false))
                .findFirst()
                .orElseThrow(() -> new AssertionError("No 'collect' call found in groupAndCount()"));

        // Must not throw UnsupportedOperationException or UnsolvedSymbolException (issue #3751).
        ResolvedType resolvedType = collectCall.calculateResolvedType();
        assertTrue(resolvedType.isReferenceType(), "Expected a reference type (Map)");
        // The outer container is Map and the value type is Long; the key type variable K may
        // remain partially unresolved until poly-expression inference is fully implemented.
        String described = resolvedType.describe();
        assertTrue(described.startsWith("java.util.Map<"), "Expected Map return type, was: " + described);
        assertTrue(described.endsWith(", java.lang.Long>"), "Expected Long value type, was: " + described);
    }

    /**
     * Verifies that a constructor reference ({@code ::new}) used as a variable initializer
     * resolves to the declared functional interface type of the variable, not to the constructed
     * type.
     *
     * <p>Before the fix, {@code TypeExtractor.visit(MethodReferenceExpr)} short-circuited all
     * {@code ::new} expressions by returning {@code scope.calculateResolvedType()} — i.e. the
     * type being constructed (e.g. {@code String}).  This is incorrect per JLS §15.13: a
     * constructor reference is a poly expression whose type is the target functional interface.
     */
    @Test
    void resolveConstructorReferenceTypeInVariableDeclarator() {
        ParserConfiguration config =
                new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));
        StaticJavaParser.setConfiguration(config);
        CompilationUnit cu = parseSample("ConstructorReference");

        List<com.github.javaparser.ast.expr.MethodReferenceExpr> refs =
                cu.getChildNodesByType(com.github.javaparser.ast.expr.MethodReferenceExpr.class);
        assertEquals(2, refs.size(), "Expected 2 constructor references in the sample");

        // Function<String, String> copyConstructor = String::new  →  Function<String, String>
        ResolvedType copyType = refs.get(0).calculateResolvedType();
        assertEquals("java.util.function.Function<java.lang.String, java.lang.String>", copyType.describe());

        // Supplier<String> noArgConstructor = String::new  →  Supplier<String>
        ResolvedType supplierType = refs.get(1).calculateResolvedType();
        assertEquals("java.util.function.Supplier<java.lang.String>", supplierType.describe());
    }

    // Related to issue #3195
    @Test
    void solveVariadicStaticGenericMethodCallCanInferFromArguments2() {
        ParserConfiguration config =
                new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(createTypeSolver()));
        StaticJavaParser.setConfiguration(config);
        MethodCallExpr methodCallExpr = getMethodCallExpr("genericMethodTest", "asList");

        ResolvedType resolvedType = methodCallExpr.calculateResolvedType();
        assertEquals("java.util.List<java.lang.String>", resolvedType.describe());
    }
}
