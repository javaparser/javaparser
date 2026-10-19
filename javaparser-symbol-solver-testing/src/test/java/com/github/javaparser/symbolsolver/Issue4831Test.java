/*
 * Copyright (C) 2011, 2013-2026 The JavaParser Team.
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

package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.types.ResolvedCaptureType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.resolution.typesolvers.TypeSolverBuilder;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Stream;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;
import org.junit.jupiter.params.provider.ValueSource;

class Issue4831Test extends AbstractSymbolResolutionTest {

    @Test
    void inferChainedLambdaParameterFromSupplierReturnType() {
        assertStringMonoChain("Supplier<? extends Mono<? extends T>>", "Mono.defer(() -> (Mono<String>) null)");
    }

    @Test
    void resolveChainedLambdaWithExplicitMethodTypeArgument() {
        assertStringMonoChain("Supplier<? extends Mono<? extends T>>", "Mono.<String>defer(() -> null)");
    }

    @Test
    void inferChainedLambdaParameterWithoutWildcards() {
        assertStringMonoChain("Supplier<Mono<T>>", "Mono.defer(() -> (Mono<String>) null)");
    }

    @Test
    void inferDeferTypeFromSupplierVariableWithNestedExtendsWildcards() {
        assertSupplierVariableReturnType("Supplier<? extends Mono<? extends T>>", "Supplier<Mono<String>>");
    }

    @Test
    void inferDeferTypeFromSupplierVariableWithOuterExtendsWildcard() {
        assertSupplierVariableReturnType("Supplier<? extends Mono<T>>", "Supplier<Mono<String>>");
    }

    @Test
    void inferDeferTypeFromSupplierVariableWithInnerExtendsWildcard() {
        assertSupplierVariableReturnType("Supplier<Mono<? extends T>>", "Supplier<Mono<? extends String>>");
    }

    @Test
    void inferTypeParameterFromExtendsBound() {
        String code = "import java.util.List;\n"
                + "class Example {\n"
                + "    static <T> T first(List<? extends T> values) { return null; }\n"
                + "    void test(List<String> values) {\n"
                + "        Example.first(values).length();\n"
                + "    }\n"
                + "}\n";

        assertResolvedCallType(code, "first", "java.lang.String");
    }

    @Test
    void inferTypeParameterThroughNestedExtendsBounds() {
        String code = "import java.util.List;\n"
                + "class Example {\n"
                + "    static <T> T firstNested(List<? extends List<? extends T>> values) { return null; }\n"
                + "    void test(List<List<String>> values) {\n"
                + "        Example.firstNested(values).length();\n"
                + "    }\n"
                + "}\n";

        assertResolvedCallType(code, "firstNested", "java.lang.String");
    }

    @Test
    void inferExtendsBoundFromSubclassWithFewerTypeParameters() {
        String code = "import java.util.List;\n"
                + "class Example {\n"
                + "    static class Pair<A, B> {}\n"
                + "    static class Single<B> extends Pair<String, B> {}\n"
                + "    static <T> T pick(T value, List<? extends Pair<String, T>> xs) { return value; }\n"
                + "    void test(List<Single<String>> xs) {\n"
                + "        String s = Example.pick(\"x\", xs);\n"
                + "    }\n"
                + "}\n";

        assertResolvedCallType(code, "pick", "java.lang.String");
    }

    @Test
    void inferExtendsBoundFromSubclassWithReorderedTypeParameters() {
        assertInheritedPairType("static class Flip<A, B> extends Pair<B, A> {}", "Flip<Integer, String>");
    }

    @Test
    void inferExtendsBoundFromSubclassWithMoreTypeParameters() {
        assertInheritedPairType("static class Extra<A, B, C> extends Pair<C, A> {}", "Extra<Integer, Long, String>");
    }

    @Test
    void inferExtendsBoundFromNonGenericSubclass() {
        assertInheritedPairType("static class Fixed extends Pair<String, Integer> {}", "Fixed");
    }

    @Test
    void inferExtendsBoundThroughMultipleInheritanceLevels() {
        assertInheritedPairType(
                "static class Mid<A, B> extends Pair<B, A> {}\n" + "    static class Leaf<C> extends Mid<C, String> {}",
                "Leaf<Integer>");
    }

    @Test
    void inferExtendsBoundFromImplementedInterface() {
        String code = "import java.util.List;\n"
                + "class Example {\n"
                + "    interface Pair<A, B> {}\n"
                + "    static class Single<B> implements Pair<String, B> {}\n"
                + "    static <T> T pick(List<? extends Pair<String, T>> xs) { return null; }\n"
                + "    void test(List<Single<Integer>> xs) { Example.pick(xs); }\n"
                + "}\n";

        assertResolvedCallType(code, "pick", "java.lang.Integer");
    }

    @Test
    void inferExtendsBoundFromReflectionBackedSubclass() {
        String code = "import java.util.List;\n"
                + "import java.util.ArrayList;\n"
                + "class Example {\n"
                + "    static <T> T pick(List<? extends List<T>> xs) { return null; }\n"
                + "    void test(List<ArrayList<Integer>> xs) { Example.pick(xs); }\n"
                + "}\n";

        assertResolvedCallType(code, "pick", "java.lang.Integer");
    }

    private void assertInheritedPairType(String subclass, String actualType) {
        String code = "import java.util.List;\n"
                + "class Example {\n"
                + "    static class Pair<A, B> {}\n"
                + "    " + subclass + "\n"
                + "    static <T> T pick(List<? extends Pair<String, T>> xs) { return null; }\n"
                + "    void test(List<" + actualType + "> xs) { Example.pick(xs); }\n"
                + "}\n";

        assertResolvedCallType(code, "pick", "java.lang.Integer");
    }

    @Test
    void inferExtendsBoundFromSingleVararg() {
        assertVarargsType("strings", "java.lang.String");
    }

    @Test
    void inferExtendsBoundFromMultipleVarargs() {
        assertVarargsType("strings, strings", "java.lang.String");
    }

    @Test
    void combineExtendsBoundsFromVarargsWithSuperclassFirst() {
        assertVarargsType("base, left", "Example.Base");
    }

    @Test
    void combineExtendsBoundsFromVarargsWithSuperclassLast() {
        assertVarargsType("left, base", "Example.Base");
    }

    @Test
    void combineExtendsBoundsFromVarargsWithSiblingTypes() {
        assertVarargsType("left, right", "Example.Base");
    }

    @Test
    void inferExtendsBoundFromVarargsArray() {
        assertVarargsType("array", "java.lang.String");
    }

    private void assertVarargsType(String arguments, String expectedType) {
        String code = "import java.util.List;\n"
                + "class Example {\n"
                + "    static class Base {}\n"
                + "    static class Left extends Base {}\n"
                + "    static class Right extends Base {}\n"
                + "    static <T> T pick(List<? extends T>... xs) { return null; }\n"
                + "    void test(List<String> strings, List<Base> base, List<Left> left, List<Right> right,"
                + " List<String>[] array) {\n"
                + "        Example.pick(" + arguments + ");\n"
                + "    }\n"
                + "}\n";

        assertResolvedCallType(code, "pick", expectedType);
    }

    @Test
    void keepConcreteTypeWhenConsumerAcceptsASupertype() {
        String code = "import java.util.List;\n"
                + "class Example {\n"
                + "    static <T> T addAndReturn(T value, List<? super T> destination) {\n"
                + "        destination.add(value);\n"
                + "        return value;\n"
                + "    }\n"
                + "    void test(Integer value, List<Object> destination) {\n"
                + "        Example.addAndReturn(value, destination).intValue();\n"
                + "    }\n"
                + "}\n";

        assertResolvedCallType(code, "addAndReturn", "java.lang.Integer");
    }

    @Test
    void inferIndependentTypeParameterAlongsideUnboundedWildcard() {
        String code = "class Example {\n"
                + "    static class Pair<A, B> {}\n"
                + "    static <A, B> B second(Pair<A, B> pair) { return null; }\n"
                + "    void test(Pair<?, String> pair) {\n"
                + "        Example.second(pair).length();\n"
                + "    }\n"
                + "}\n";

        assertResolvedCallType(code, "second", "java.lang.String");
    }

    @Test
    void resolveMemberThroughExtendsBoundOnActualArgument() {
        String code = "import java.util.List;\n"
                + "class Example {\n"
                + "    static <T> T first(List<T> values) { return null; }\n"
                + "    void test(List<? extends Number> values) {\n"
                + "        Example.first(values).intValue();\n"
                + "    }\n"
                + "}\n";
        CompilationUnit cu = parse(code);
        MethodCallExpr call = findCall(cu, "intValue");

        assertEquals("int", call.calculateResolvedType().describe());
        assertEquals("java.lang.Number", call.resolve().declaringType().getQualifiedName());
    }

    @Test
    void inferArrayComponentType() {
        String code = "class Example {\n"
                + "    static <T> T[] identity(T[] values) { return values; }\n"
                + "    void test(String[] values) {\n"
                + "        Example.identity(values);\n"
                + "    }\n"
                + "}\n";

        assertResolvedCallType(code, "identity", "java.lang.String[]");
    }

    @Test
    void boxPrimitiveTypeArgument() {
        String code = "class Example {\n"
                + "    static <T> T identity(T value) { return value; }\n"
                + "    void test() {\n"
                + "        Example.identity(1);\n"
                + "    }\n"
                + "}\n";

        assertResolvedCallType(code, "identity", "java.lang.Integer");
    }

    @Test
    void keepNarrowerTypeWhenSuperWildcardAcceptsNumber() {
        String code = "import java.util.function.Consumer;\n"
                + "class Example {\n"
                + "    static <T> T acceptAndReturn(T value, Consumer<? super T> consumer) {\n"
                + "        consumer.accept(value);\n"
                + "        return value;\n"
                + "    }\n"
                + "    void test(Integer value, Consumer<Number> consumer) {\n"
                + "        Example.acceptAndReturn(value, consumer);\n"
                + "    }\n"
                + "}\n";

        assertResolvedCallType(code, "acceptAndReturn", "java.lang.Integer");
    }

    @Test
    void inferNoSpecificTypeFromUnboundedWildcard() {
        String code = "import java.util.List;\n"
                + "class Example {\n"
                + "    static <T> T unknown(List<?> values) { return null; }\n"
                + "    void test(List<String> values) {\n"
                + "        Example.unknown(values);\n"
                + "    }\n"
                + "}\n";
        ResolvedType type = findCall(parse(code), "unknown").calculateResolvedType();

        assertTrue(
                type.isTypeVariable() || type.describe().equals("java.lang.Object"),
                () -> "Unconstrained T may remain unresolved or default to Object, but was " + type.describe());
    }

    @Test
    void keepInferredTypeWhenAnotherParameterHasUnboundedWildcard() {
        String code = "import java.util.List;\n"
                + "class Example {\n"
                + "    static <T> T keep(T value, List<?> ignored) { return value; }\n"
                + "    void test(Integer value, List<String> ignored) {\n"
                + "        Example.keep(value, ignored);\n"
                + "    }\n"
                + "}\n";

        assertResolvedCallType(code, "keep", "java.lang.Integer");
    }

    @Test
    void combineExtendsConstraintsWhenSubtypeIsLast() {
        assertCommonTypeFromExtendsConstraints("base, derived");
    }

    @Test
    void combineExtendsConstraintsWhenSupertypeIsLast() {
        assertCommonTypeFromExtendsConstraints("derived, base");
    }

    @Test
    void inferThreeConstraintsWithSuperclassFirst() {
        assertResolvedCallType(threeConstraintCode("base, derived, derived"), "choose3", "Example.Base");
    }

    @Test
    void inferThreeConstraintsWithSuperclassInMiddle() {
        assertResolvedCallType(threeConstraintCode("derived, base, derived"), "choose3", "Example.Base");
    }

    @Test
    void inferCommonSuperclassOfSiblings() {
        String code = "import java.util.List;\n"
                + "class Example {\n"
                + "    static class Base {}\n"
                + "    static class Left extends Base {}\n"
                + "    static class Right extends Base {}\n"
                + "    static <T> T choose(List<? extends T> a,"
                + " List<? extends T> b) { return null; }\n"
                + "    void test(List<Left> left, List<Right> right) {\n"
                + "        Example.choose(left, right);\n"
                + "    }\n"
                + "}\n";

        assertResolvedCallType(code, "choose", "Example.Base");
    }

    @Test
    void inferRepeatedIdenticalConstraints() {
        assertResolvedCallType(threeConstraintCode("base, base, base"), "choose3", "Example.Base");
    }

    private String threeConstraintCode(String arguments) {
        return "import java.util.List;\n"
                + "class Example {\n"
                + "    static class Base {}\n"
                + "    static class Derived extends Base {}\n"
                + "    static <T> T choose3("
                + "List<? extends T> a,"
                + " List<? extends T> b,"
                + " List<? extends T> c) { return null; }\n"
                + "    void test(List<Base> base, List<Derived> derived) {\n"
                + "        Example.choose3(" + arguments + ");\n"
                + "    }\n"
                + "}\n";
    }

    @Test
    void preserveEqualityConstraintWithCompatibleLowerBound() {
        String code = "import java.util.List;\n"
                + "class Example {\n"
                + "    static class Base {}\n"
                + "    static class Derived extends Base {}\n"
                + "    static <T> T choose("
                + "List<T> exact,"
                + " List<? extends T> lower) { return null; }\n"
                + "    void test(List<Base> base, List<Derived> derived) {\n"
                + "        Example.choose(base, derived);\n"
                + "    }\n"
                + "}\n";

        assertResolvedCallType(code, "choose", "Example.Base");
    }

    @Test
    void preserveEqualityConstraintWhenLowerBoundComesFirst() {
        String code = "import java.util.List;\n"
                + "class Example {\n"
                + "    static class Base {}\n"
                + "    static class Derived extends Base {}\n"
                + "\n"
                + "    static <T> T choose(\n"
                + "            List<? extends T> lower,\n"
                + "            List<T> exact) {\n"
                + "        return null;\n"
                + "    }\n"
                + "\n"
                + "    void test(List<Derived> derived, List<Base> base) {\n"
                + "        Example.choose(derived, base);\n"
                + "    }\n"
                + "}\n";

        assertResolvedCallType(code, "choose", "Example.Base");
    }

    @Test
    void preserveTypeWhenSuperWildcardIsLast() {
        String code = "import java.util.List;\n"
                + "class Example {\n"
                + "    static <T> T choose("
                + "List<T> exact, List<? super T> sink) {\n"
                + "        return null;\n"
                + "    }\n"
                + "    void test(List<Integer> exact, List<Number> sink) {\n"
                + "        Example.choose(exact, sink);\n"
                + "    }\n"
                + "}\n";

        assertResolvedCallType(code, "choose", "java.lang.Integer");
    }

    @Test
    void preserveTypeWhenSuperWildcardIsFirst() {
        String code = "import java.util.List;\n"
                + "class Example {\n"
                + "    static <T> T choose("
                + "List<? super T> sink, List<T> exact) {\n"
                + "        return null;\n"
                + "    }\n"
                + "    void test(List<Object> sink, List<Integer> exact) {\n"
                + "        Example.choose(sink, exact);\n"
                + "    }\n"
                + "}\n";

        assertResolvedCallType(code, "choose", "java.lang.Integer");
    }

    @Test
    void preserveTypeWithActualSuperWildcard() {
        String code = "import java.util.List;\n"
                + "class Example {\n"
                + "    static <T> T choose("
                + "List<? super T> sink, List<T> exact) {\n"
                + "        return null;\n"
                + "    }\n"
                + "    void test("
                + "List<? super Integer> sink,"
                + " List<Integer> exact) {\n"
                + "        Example.choose(sink, exact);\n"
                + "    }\n"
                + "}\n";

        assertResolvedCallType(code, "choose", "java.lang.Integer");
    }

    private void assertCommonTypeFromExtendsConstraints(String arguments) {
        String code = "import java.util.List;\n"
                + "class Example {\n"
                + "    static class Base {}\n"
                + "    static class Derived extends Base {}\n"
                + "    static <T> T choose(List<? extends T> first, List<? extends T> second) {\n"
                + "        return null;\n"
                + "    }\n"
                + "    void test(List<Base> base, List<Derived> derived) {\n"
                + "        Example.choose(" + arguments + ");\n"
                + "    }\n"
                + "}\n";

        assertResolvedCallType(code, "choose", "Example.Base");
    }

    private void assertSupplierVariableReturnType(String formalSupplierType, String actualSupplierType) {
        String code = "import java.util.function.Supplier;\n"
                + "class Foo {\n"
                + "    static abstract class Mono<T> {\n"
                + "        static <T> Mono<T> defer(" + formalSupplierType + " supplier) { return null; }\n"
                + "    }\n"
                + "    void test(" + actualSupplierType + " supplier) {\n"
                + "        Mono.defer(supplier);\n"
                + "    }\n"
                + "}\n";

        assertResolvedCallType(code, "defer", "Foo.Mono<java.lang.String>");
    }

    private void assertStringMonoChain(String supplierType, String deferCall) {
        String code = "import java.util.function.Consumer;\n"
                + "import java.util.function.Supplier;\n"
                + "class Foo {\n"
                + "    private static abstract class Mono<T> {\n"
                + "        public static <T> Mono<T> defer(" + supplierType + " supplier) {\n"
                + "            return null;\n"
                + "        }\n"
                + "        public final void consume(Consumer<? super T> consumer) {}\n"
                + "    }\n"
                + "    public void test() {\n"
                + "        " + deferCall + ".consume(s -> s.length());\n"
                + "    }\n"
                + "}\n";
        CompilationUnit cu = parse(code);

        List<MethodCallExpr> calls = cu.findAll(MethodCallExpr.class);
        assertEquals(3, calls.size());
        Map<String, ResolvedType> resolvedTypes = new HashMap<>();

        calls.forEach(call -> resolvedTypes.put(call.getNameAsString(), call.calculateResolvedType()));

        assertEquals("Foo.Mono<java.lang.String>", resolvedTypes.get("defer").describe());
        assertEquals("int", resolvedTypes.get("length").describe());
        assertEquals("void", resolvedTypes.get("consume").describe());

        MethodCallExpr lengthCall = calls.stream()
                .filter(call -> call.getNameAsString().equals("length"))
                .findFirst()
                .orElseThrow(AssertionError::new);

        ResolvedMethodDeclaration lengthMethod = lengthCall.resolve();
        assertEquals("java.lang.String", lengthMethod.declaringType().getQualifiedName());
    }

    private void assertResolvedCallType(String code, String methodName, String expectedType) {
        MethodCallExpr call = findCall(parse(code), methodName);
        assertEquals(expectedType, call.calculateResolvedType().describe());
    }

    private CompilationUnit parse(String code) {
        ParserConfiguration configuration = new ParserConfiguration()
                .setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_8)
                .setSymbolResolver(new JavaSymbolSolver(
                        new TypeSolverBuilder().withCurrentClassloader().build()));
        ParseResult<CompilationUnit> result = new JavaParser(configuration).parse(code);
        assertTrue(result.isSuccessful(), () -> result.getProblems().toString());
        return result.getResult().orElseThrow(AssertionError::new);
    }

    private MethodCallExpr findCall(CompilationUnit cu, String methodName) {
        return cu.findFirst(MethodCallExpr.class, call -> call.getNameAsString().equals(methodName))
                .orElseThrow(AssertionError::new);
    }

    // Arrays, inheritance, caller type variables, and expanded varargs.
    @ParameterizedTest
    @ValueSource(strings = {"Other<Integer>", "Pair<Integer, Integer>"})
    void rejectIncompatibleExtendsWildcard(String elementType) {
        String source = boundaryCode(
                "static <T> T pick(List<? extends Pair<String, T>> xs) { return null; }",
                "List<? extends " + elementType + "> xs",
                "xs",
                "static class Other<B> {}",
                "");
        assertThrows(
                UnsolvedSymbolException.class, () -> findCall(source, "pick").calculateResolvedType());
    }

    // Expected types were checked with javac --release 8, without an assignment target.
    @ParameterizedTest(name = "{0}")
    @MethodSource("boundaryCases")
    void inferBoundaryCase(String name, String source, String expectedType) {
        assertResolvedCallType(source, "pick", expectedType);
    }

    private static Stream<Arguments> boundaryCases() {
        return Stream.of(
                Arguments.of(
                        "reference array as extends argument",
                        boundaryCode(
                                "static <T> T pick(List<? extends T> xs) { return null; }", "List<String[]> xs", "xs"),
                        "java.lang.String[]"),
                Arguments.of(
                        "primitive array as extends argument",
                        boundaryCode(
                                "static <T> T pick(List<? extends T> xs) { return null; }", "List<int[]> xs", "xs"),
                        "int[]"),
                Arguments.of(
                        "array component under extends",
                        boundaryCode(
                                "static <T> T pick(List<? extends T[]> xs) { return null; }",
                                "List<String[]> xs",
                                "xs"),
                        "java.lang.String"),
                Arguments.of(
                        "nested extends array",
                        boundaryCode(
                                "static <T> T pick(List<? extends List<? extends T>> xs) { return null; }",
                                "List<List<String[]>> xs",
                                "xs"),
                        "java.lang.String[]"),
                Arguments.of(
                        "caller type variable under extends",
                        boundaryCode(
                                "static <T> T pick(List<? extends T> xs) { return null; }",
                                "List<U> xs",
                                "xs",
                                "",
                                "<U extends Number>"),
                        "U"),
                Arguments.of(
                        "caller type variable bounded by pair",
                        boundaryCode(
                                "static <T> T pick(List<? extends Pair<String,T>> xs) { return null; }",
                                "List<U> xs",
                                "xs",
                                "",
                                "<U extends Pair<String,Integer>>"),
                        "java.lang.Integer"),
                Arguments.of(
                        "caller type variable bounded by list",
                        boundaryCode(
                                "static <T> T pick(List<? extends T> xs) { return null; }",
                                "U xs",
                                "xs",
                                "",
                                "<U extends List<String>>"),
                        "java.lang.String"),
                Arguments.of(
                        "intersection bound with generic interface",
                        boundaryCode(
                                "static <T> T pick(List<? extends T> xs) { return null; }",
                                "U xs",
                                "xs",
                                "",
                                "<U extends Base & List<String>>"),
                        "java.lang.String"),
                Arguments.of(
                        "inherited nested type argument",
                        boundaryCode(
                                "static <T> T pick(List<? extends Pair<String,T>> xs) { return null; }",
                                "List<Nested<Integer>> xs",
                                "xs",
                                "static class Nested<B> extends Pair<String,List<B>> {}",
                                ""),
                        "java.util.List<java.lang.Integer>"),
                Arguments.of(
                        "diamond interface ancestry",
                        boundaryCode(
                                "static <T> T pick(List<? extends Root<String,T>> xs) { return null; }",
                                "List<Both<Integer>> xs",
                                "xs",
                                "interface Root<A,B> {} interface L<B> extends Root<String,B> {} interface R<B> extends Root<String,B> {} static class Both<B> implements L<B>, R<B> {}",
                                ""),
                        "java.lang.Integer"),
                Arguments.of(
                        "inherited array type argument",
                        boundaryCode(
                                "static <T> T pick(List<? extends Pair<String,T>> xs) { return null; }",
                                "List<ArraysOf<Integer>> xs",
                                "xs",
                                "static class ArraysOf<B> extends Pair<String,B[]> {}",
                                ""),
                        "java.lang.Integer[]"),
                Arguments.of(
                        "generic supplier implementation",
                        boundaryCode(
                                "static <T> T pick(Supplier<? extends T> xs) { return null; }",
                                "S<String> xs",
                                "xs",
                                "static class S<B> implements Supplier<B> { public B get() { return null; } }",
                                ""),
                        "java.lang.String"),
                Arguments.of(
                        "fixed supplier implementation",
                        boundaryCode(
                                "static <T> T pick(Supplier<? extends T> xs) { return null; }",
                                "S xs",
                                "xs",
                                "static class S implements Supplier<String> { public String get() { return null; } }",
                                ""),
                        "java.lang.String"),
                Arguments.of(
                        "mixed value lower bounds left, base",
                        boundaryCode(
                                "static <T> T pick(T value, List<? extends T> xs) { return null; }",
                                "Left left, List<Base> base",
                                "left, base"),
                        "Example.Base"),
                Arguments.of(
                        "mixed value lower bounds base, left",
                        boundaryCode(
                                "static <T> T pick(T value, List<? extends T> xs) { return null; }",
                                "Base base, List<Left> left",
                                "base, left"),
                        "Example.Base"),
                Arguments.of(
                        "mixed value lower bounds reversed parameters",
                        boundaryCode(
                                "static <T> T pick(List<? extends T> xs, T value) { return null; }",
                                "List<Base> base, Left left",
                                "base, left"),
                        "Example.Base"),
                Arguments.of(
                        "null does not widen lower bound",
                        boundaryCode(
                                "static <T> T pick(T value, List<? extends T> xs) { return null; }",
                                "List<String> xs",
                                "null, xs"),
                        "java.lang.String"),
                Arguments.of(
                        "direct value lower bounds base, left",
                        boundaryCode(
                                "static <T> T pick(T a, T b) { return null; }", "Base base, Left left", "base, left"),
                        "Example.Base"),
                Arguments.of(
                        "direct value lower bounds left, base",
                        boundaryCode(
                                "static <T> T pick(T a, T b) { return null; }", "Base base, Left left", "left, base"),
                        "Example.Base"),
                Arguments.of(
                        "fixed prefix varargs \"tag\", strings",
                        boundaryCode(
                                "static <T> T pick(String tag, List<? extends T>... xs) { return null; }",
                                "List<String> strings, List<String>[] array",
                                "\"tag\", strings"),
                        "java.lang.String"),
                Arguments.of(
                        "fixed prefix varargs \"tag\", strings, strings",
                        boundaryCode(
                                "static <T> T pick(String tag, List<? extends T>... xs) { return null; }",
                                "List<String> strings, List<String>[] array",
                                "\"tag\", strings, strings"),
                        "java.lang.String"),
                Arguments.of(
                        "fixed prefix varargs \"tag\", array",
                        boundaryCode(
                                "static <T> T pick(String tag, List<? extends T>... xs) { return null; }",
                                "List<String> strings, List<String>[] array",
                                "\"tag\", array"),
                        "java.lang.String"),
                Arguments.of(
                        "fixed constraint varargs base",
                        boundaryCode(
                                "static <T> T pick(List<? extends T> first, List<? extends T>... rest) { return null; }",
                                "List<Base> base, List<Left> left, List<Left>[] array",
                                "base"),
                        "Example.Base"),
                Arguments.of(
                        "fixed constraint varargs base, left",
                        boundaryCode(
                                "static <T> T pick(List<? extends T> first, List<? extends T>... rest) { return null; }",
                                "List<Base> base, List<Left> left, List<Left>[] array",
                                "base, left"),
                        "Example.Base"),
                Arguments.of(
                        "fixed constraint varargs base, left, left",
                        boundaryCode(
                                "static <T> T pick(List<? extends T> first, List<? extends T>... rest) { return null; }",
                                "List<Base> base, List<Left> left, List<Left>[] array",
                                "base, left, left"),
                        "Example.Base"),
                Arguments.of(
                        "fixed constraint varargs base, array",
                        boundaryCode(
                                "static <T> T pick(List<? extends T> first, List<? extends T>... rest) { return null; }",
                                "List<Base> base, List<Left> left, List<Left>[] array",
                                "base, array"),
                        "Example.Base"),
                Arguments.of(
                        "direct varargs lower bounds base, left",
                        boundaryCode(
                                "static <T> T pick(T... xs) { return null; }", "Base base, Left left", "base, left"),
                        "Example.Base"),
                Arguments.of(
                        "direct varargs lower bounds left, base",
                        boundaryCode(
                                "static <T> T pick(T... xs) { return null; }", "Base base, Left left", "left, base"),
                        "Example.Base"),
                Arguments.of(
                        "extends array in varargs",
                        boundaryCode(
                                "static <T> T pick(List<? extends T>... xs) { return null; }",
                                "List<String[]> xs",
                                "xs, xs"),
                        "java.lang.String[]"),
                Arguments.of(
                        "null vararg does not widen",
                        boundaryCode(
                                "static <T> T pick(List<? extends T>... xs) { return null; }",
                                "List<String> xs",
                                "xs, null"),
                        "java.lang.String"),
                Arguments.of(
                        "primitive varargs array",
                        boundaryCode("static <T> T pick(T... xs) { return null; }", "int[] xs", "xs"),
                        "int[]"),
                Arguments.of(
                        "reference varargs array",
                        boundaryCode("static <T> T pick(T... xs) { return null; }", "String[] xs", "xs"),
                        "java.lang.String"),
                Arguments.of(
                        "multidimensional varargs array",
                        boundaryCode("static <T> T pick(T... xs) { return null; }", "String[][] xs", "xs"),
                        "java.lang.String[]"),
                Arguments.of(
                        "invariant constraint with direct subtype",
                        boundaryCode(
                                "static <T> T pick(List<T> exact, T value) { return null; }",
                                "List<Base> exact, Left left",
                                "exact, left"),
                        "Example.Base"),
                Arguments.of(
                        "invariant constraint after direct subtype",
                        boundaryCode(
                                "static <T> T pick(T value, List<T> exact) { return null; }",
                                "List<Base> exact, Left left",
                                "left, exact"),
                        "Example.Base"),
                Arguments.of(
                        "lambda returning reference array",
                        boundaryCode(
                                "static <T> T pick(Supplier<? extends T> supplier) { return null; }",
                                "",
                                "() -> new String[0]"),
                        "java.lang.String[]"),
                Arguments.of(
                        "lambda returning primitive array",
                        boundaryCode(
                                "static <T> T pick(Supplier<? extends T> supplier) { return null; }",
                                "",
                                "() -> new int[0]"),
                        "int[]"),
                Arguments.of(
                        "method reference returning reference array",
                        boundaryCode(
                                "static <T> T pick(Supplier<? extends T> supplier) { return null; }",
                                "",
                                "Example::strings",
                                "static String[] strings() { return null; }",
                                ""),
                        "java.lang.String[]"),
                Arguments.of(
                        "array component is caller type variable",
                        boundaryCode(
                                "static <T> T pick(List<? extends T[]> xs) { return null; }",
                                "List<U[]> xs",
                                "xs",
                                "",
                                "<U extends Number>"),
                        "U"));
    }

    @ParameterizedTest(name = "{0}")
    @MethodSource("nestedWildcardSubtypeCases")
    void inferNestedWildcardSubtype(String name, String source, String expectedType) {
        assertResolvedCallType(source, "pick", expectedType);
    }

    private static Stream<Arguments> nestedWildcardSubtypeCases() {
        return Stream.of(
                Arguments.of(
                        "wildcard bounded subclass",
                        boundaryCode(
                                "static <T> T pick(List<? extends Pair<String,T>> xs) { return null; }",
                                "List<? extends Single<Integer>> xs",
                                "xs"),
                        "java.lang.Integer"),
                Arguments.of(
                        "lambda returning parameterized subclass",
                        boundaryCode(
                                "static <T> T pick(Supplier<? extends Pair<String,T>> supplier) { return null; }",
                                "",
                                "() -> new Single<Integer>()"),
                        "java.lang.Integer"),
                Arguments.of(
                        "method reference returning parameterized subclass",
                        boundaryCode(
                                "static <T> T pick(Supplier<? extends Pair<String,T>> supplier) { return null; }",
                                "",
                                "Example::single",
                                "static Single<Integer> single() { return null; }",
                                ""),
                        "java.lang.Integer"));
    }

    private static String boundaryCode(String method, String parameters, String arguments) {
        return boundaryCode(method, parameters, arguments, "", "");
    }

    private static String boundaryCode(
            String method, String parameters, String arguments, String declarations, String generics) {
        return "import java.util.*;\n"
                + "import java.util.function.*;\n"
                + "class Example {\n"
                + "    static class Base {}\n"
                + "    static class Left extends Base {}\n"
                + "    static class Right extends Base {}\n"
                + "    static class Pair<A, B> {}\n"
                + "    static class Single<B> extends Pair<String, B> {}\n"
                + declarations + "\n"
                + method + "\n"
                + generics + " void test(" + parameters + ") { Example.pick(" + arguments + "); }\n"
                + "}\n";
    }

    // Upper bounds and capture conversion of lower-bounded wildcards.
    // All expected types are for standalone expressions, without assignment target typing.
    @ParameterizedTest(name = "{0}")
    @MethodSource("upperBounds")
    void inferUpperBounds(String name, String method, String parameters, String arguments, String expected) {
        assertEquals(
                expected,
                findCall(superWildcardCode(method, parameters, "Example.pick(" + arguments + ")"), "pick")
                        .calculateResolvedType()
                        .describe());
    }

    private static Stream<Arguments> upperBounds() {
        return Stream.of(
                Arguments.of(
                        "single concrete upper",
                        "static <T> T pick(List<? super T> xs) { return null; }",
                        "List<String> xs",
                        "xs",
                        "java.lang.String"),
                Arguments.of(
                        "single array upper",
                        "static <T> T pick(List<? super T> xs) { return null; }",
                        "List<String[]> xs",
                        "xs",
                        "java.lang.String[]"),
                Arguments.of(
                        "single primitive array upper",
                        "static <T> T pick(List<? super T> xs) { return null; }",
                        "List<int[]> xs",
                        "xs",
                        "int[]"),
                Arguments.of(
                        "actual super wildcard",
                        "static <T> T pick(List<? super T> xs) { return null; }",
                        "List<? super String> xs",
                        "xs",
                        "capture of ? super java.lang.String"),
                Arguments.of(
                        "multiple upper bounds",
                        "static <T> T pick(List<? super T> a, List<? super T> b) { return null; }",
                        "List<Object> a, List<String> b",
                        "a,b",
                        "java.lang.String"),
                Arguments.of(
                        "reversed upper bounds",
                        "static <T> T pick(List<? super T> a, List<? super T> b) { return null; }",
                        "List<String> a, List<Object> b",
                        "a,b",
                        "java.lang.String"),
                Arguments.of(
                        "repeated upper bounds",
                        "static <T> T pick(List<? super T> a, List<? super T> b) { return null; }",
                        "List<String> a, List<String> b",
                        "a,b",
                        "java.lang.String"),
                Arguments.of(
                        "declared upper bound",
                        "static <T extends Number> T pick(List<? super T> xs) { return null; }",
                        "List<Object> xs",
                        "xs",
                        "java.lang.Number"),
                Arguments.of(
                        "more specific upper than declaration",
                        "static <T extends Number> T pick(List<? super T> xs) { return null; }",
                        "List<Integer> xs",
                        "xs",
                        "java.lang.Integer"),
                Arguments.of(
                        "null and upper",
                        "static <T> T pick(T value, List<? super T> xs) { return null; }",
                        "List<String> xs",
                        "null,xs",
                        "java.lang.String"),
                Arguments.of(
                        "lower wins over upper",
                        "static <T> T pick(T value, List<? super T> xs) { return null; }",
                        "List<Number> xs",
                        "1,xs",
                        "java.lang.Integer"),
                Arguments.of(
                        "extends and super",
                        "static <T> T pick(List<? extends T> a, List<? super T> b) { return null; }",
                        "List<Integer> a, List<Number> b",
                        "a,b",
                        "java.lang.Integer"),
                Arguments.of(
                        "upper before equality",
                        "static <T> T pick(List<? super T> b, List<T> a) { return null; }",
                        "List<Integer> a, List<Number> b",
                        "b,a",
                        "java.lang.Integer"),
                Arguments.of(
                        "single super vararg",
                        "static <T> T pick(List<? super T>... xs) { return null; }",
                        "List<String> xs",
                        "xs",
                        "java.lang.String"),
                Arguments.of(
                        "multiple super varargs",
                        "static <T> T pick(List<? super T>... xs) { return null; }",
                        "List<String> a, List<Object> b",
                        "a,b",
                        "java.lang.String"),
                Arguments.of(
                        "reversed super varargs",
                        "static <T> T pick(List<? super T>... xs) { return null; }",
                        "List<String> a, List<Object> b",
                        "b,a",
                        "java.lang.String"),
                Arguments.of(
                        "array super varargs",
                        "static <T> T pick(List<? super T>... xs) { return null; }",
                        "List<String>[] xs",
                        "xs",
                        "java.lang.String"),
                Arguments.of(
                        "fixed and super varargs",
                        "static <T> T pick(T value, List<? super T>... xs) { return null; }",
                        "List<Number> xs",
                        "1,xs,xs",
                        "java.lang.Integer"),
                Arguments.of(
                        "nested invariant upper",
                        "static <T> T pick(List<? super List<T>> xs) { return null; }",
                        "List<List<String>> xs",
                        "xs",
                        "java.lang.String"),
                Arguments.of(
                        "upper aligns formal subtype",
                        "static <T> T pick(List<? super List<T>> xs) { return null; }",
                        "List<Collection<String>> xs",
                        "xs",
                        "java.lang.String"),
                Arguments.of(
                        "upper aligns fewer parameters",
                        "static <T> T pick(List<? super Single<T>> xs) { return null; }",
                        "List<Pair<String,Integer>> xs",
                        "xs",
                        "java.lang.Integer"),
                Arguments.of(
                        "upper aligns reordered parameters",
                        "static <T> T pick(List<? super Flip<T,String>> xs) { return null; }",
                        "List<Pair<String,Integer>> xs",
                        "xs",
                        "java.lang.Integer"),
                Arguments.of(
                        "super array component",
                        "static <T> T pick(List<? super T[]> xs) { return null; }",
                        "List<String[]> xs",
                        "xs",
                        "java.lang.String"));
    }

    @Test
    void upperBoundResolvesStringMember() {
        MethodCallExpr call = findCall(
                superWildcardCode(
                        "static <T> T pick(List<? super T> xs) { return null; }",
                        "List<String> xs",
                        "Example.pick(xs).length()"),
                "length");
        assertEquals("int", call.calculateResolvedType().describe());
        assertEquals("java.lang.String.length()", call.resolve().getQualifiedSignature());
    }

    @Test
    void upperBoundResolvesIntegerMember() {
        MethodCallExpr call = findCall(
                superWildcardCode(
                        "static <T extends Number> T pick(List<? super T> xs) { return null; }",
                        "List<Integer> xs",
                        "Example.pick(xs).compareTo(1)"),
                "compareTo");
        assertEquals("int", call.calculateResolvedType().describe());
        assertEquals("java.lang.Integer", call.resolve().declaringType().getQualifiedName());
    }

    @Test
    void actualSuperWildcardDoesNotExposeLowerBoundEvenForSuperFormal() {
        MethodCallExpr call = findCall(
                superWildcardCode(
                        "static <T> T pick(List<? super T> xs) { return null; }",
                        "List<? super String> xs",
                        "Example.pick(xs).length()"),
                "length");
        assertThrows(UnsolvedSymbolException.class, call::calculateResolvedType);
        assertThrows(UnsolvedSymbolException.class, call::resolve);
    }

    @Test
    void capturePreservesBothBounds() {
        ResolvedType type = findCall(
                        superWildcardCode(
                                "static <T> T pick(List<T> xs) { return null; }",
                                "List<? super Integer> xs",
                                "Example.pick(xs)"),
                        "pick")
                .calculateResolvedType();
        assertTrue(type instanceof ResolvedCaptureType);
        ResolvedCaptureType capture = (ResolvedCaptureType) type;
        assertEquals("java.lang.Integer", capture.getWildcard().getBoundedType().describe());
        assertEquals(
                "java.lang.Object",
                capture.asTypeParameter().getBounds().get(0).getType().describe());
        assertEquals("java.lang.Object", capture.erasure().describe());
        assertEquals("Ljava/lang/Object;", capture.toDescriptor());
    }

    @ParameterizedTest
    @ValueSource(strings = {"intValue", "compareTo"})
    void captureCannotReadIntegerMembers(String member) {
        String expression = "Example.pick(xs)." + member + (member.equals("compareTo") ? "(1)" : "()");
        MethodCallExpr call = findCall(
                superWildcardCode(
                        "static <T> T pick(List<T> xs) { return null; }", "List<? super Integer> xs", expression),
                member);
        assertThrows(UnsolvedSymbolException.class, call::calculateResolvedType);
        assertThrows(UnsolvedSymbolException.class, call::resolve);
    }

    @Test
    void captureCanReadObjectMembers() {
        MethodCallExpr call = findCall(
                superWildcardCode(
                        "static <T> T pick(List<T> xs) { return null; }",
                        "List<? super Integer> xs",
                        "Example.pick(xs).toString()"),
                "toString");
        assertEquals("java.lang.String", call.calculateResolvedType().describe());
        assertEquals("java.lang.Object", call.resolve().declaringType().getQualifiedName());
    }

    @Test
    void captureUsesDeclaredUpperBound() {
        MethodCallExpr call = findCall(
                superWildcardCode(
                        "static <T extends Number> T pick(Box<T> xs) { return null; }",
                        "Box<? super Integer> xs",
                        "Example.pick(xs).doubleValue()"),
                "doubleValue");
        assertEquals("double", call.calculateResolvedType().describe());
        assertEquals("java.lang.Number", call.resolve().declaringType().getQualifiedName());
    }

    @Test
    void boundedCaptureCannotReadLowerBoundMembers() {
        MethodCallExpr call = findCall(
                superWildcardCode(
                        "static <T extends Number> T pick(Box<T> xs) { return null; }",
                        "Box<? super Integer> xs",
                        "Example.pick(xs).compareTo(1)"),
                "compareTo");
        assertThrows(UnsolvedSymbolException.class, call::calculateResolvedType);
        assertThrows(UnsolvedSymbolException.class, call::resolve);
    }

    @Test
    void captureUnderExtendsDoesNotBecomeLowerBound() {
        MethodCallExpr call = findCall(
                superWildcardCode(
                        "static <T> T pick(List<? extends T> xs) { return null; }",
                        "List<? super Integer> xs",
                        "Example.pick(xs).intValue()"),
                "intValue");
        assertThrows(UnsolvedSymbolException.class, call::calculateResolvedType);
    }

    @Test
    void capturedContainerRejectsInvalidRead() {
        MethodCallExpr call = findCall(
                superWildcardCode(
                        "static <T> List<T> pick(List<T> xs) { return xs; }",
                        "List<? super Integer> xs",
                        "Example.pick(xs).get(0).intValue()"),
                "intValue");
        assertThrows(UnsolvedSymbolException.class, call::calculateResolvedType);
        assertThrows(UnsolvedSymbolException.class, call::resolve);
    }

    @ParameterizedTest
    @ValueSource(strings = {"1", "null"})
    void capturedContainerAcceptsLowerBoundWrites(String value) {
        MethodCallExpr call = findCall(
                superWildcardCode(
                        "static <T> List<T> pick(List<T> xs) { return xs; }",
                        "List<? super Integer> xs",
                        "Example.pick(xs).add(" + value + ")"),
                "add");
        assertEquals("boolean", call.calculateResolvedType().describe());
        assertEquals("add", call.resolve().getName());
    }

    @ParameterizedTest
    @ValueSource(strings = {"new Object()", "1.5", "\"wrong\""})
    void capturedContainerRejectsInvalidWrites(String value) {
        MethodCallExpr call = findCall(
                superWildcardCode(
                        "static <T> List<T> pick(List<T> xs) { return xs; }",
                        "List<? super Integer> xs",
                        "Example.pick(xs).add(" + value + ")"),
                "add");
        assertThrows(UnsolvedSymbolException.class, call::calculateResolvedType);
        assertThrows(UnsolvedSymbolException.class, call::resolve);
    }

    @ParameterizedTest
    @ValueSource(booleans = {false, true})
    void intersectionUpperBoundsResolveMembers(boolean reversed) {
        String source = superWildcardCode(
                "static <T> T pick(List<? super T> a, List<? super T> b) { return null; }",
                "List<CharSequence> a, List<java.io.Serializable> b",
                "Example.pick(" + (reversed ? "b,a" : "a,b") + ").length()");
        MethodCallExpr call = findCall(source, "length");
        assertEquals("int", call.calculateResolvedType().describe());
        assertEquals("java.lang.CharSequence", call.resolve().declaringType().getQualifiedName());
    }

    @Test
    void callerTypeVariableRemainsAnUpperBound() {
        String source = superWildcardCode(
                        "static <T> T pick(List<? super T> xs) { return null; }",
                        "List<U> xs",
                        "Example.pick(xs).doubleValue()")
                .replace("void test(", "<U extends Number> void test(");
        assertEquals("U", findCall(source, "pick").calculateResolvedType().describe());
        assertEquals(
                "double",
                findCall(source, "doubleValue").calculateResolvedType().describe());
        assertEquals(
                "java.lang.Number",
                findCall(source, "doubleValue").resolve().declaringType().getQualifiedName());
    }

    @Test
    void rejectInconsistentLowerAndUpperBounds() {
        MethodCallExpr call = findCall(
                superWildcardCode(
                        "static <T> T pick(T value, List<? super T> xs) { return null; }",
                        "List<String> xs",
                        "Example.pick(1, xs)"),
                "pick");
        assertThrows(UnsolvedSymbolException.class, call::calculateResolvedType);
    }

    @Test
    void rejectInconsistentDeclaredUpperBound() {
        MethodCallExpr call = findCall(
                superWildcardCode(
                        "static <T extends Number> T pick(List<? super T> xs) { return null; }",
                        "List<String> xs",
                        "Example.pick(xs)"),
                "pick");
        assertThrows(UnsolvedSymbolException.class, call::calculateResolvedType);
    }

    @Test
    void captureKeepsSubclassUpperBoundWhenMatchingAncestor() {
        String source = superWildcardCode(
                "static <T> T pick(List<T> xs) { return null; }",
                "Numbers<? super Integer> xs",
                "Example.pick(xs).doubleValue()");
        MethodCallExpr call = findCall(source, "doubleValue");
        assertEquals("double", call.calculateResolvedType().describe());
        assertEquals("java.lang.Number", call.resolve().declaringType().getQualifiedName());
    }

    @Test
    void inheritedCaptureStillRejectsLowerBoundMembers() {
        MethodCallExpr call = findCall(
                superWildcardCode(
                        "static <T> T pick(List<T> xs) { return null; }",
                        "Numbers<? super Integer> xs",
                        "Example.pick(xs).compareTo(1)"),
                "compareTo");
        assertThrows(UnsolvedSymbolException.class, call::calculateResolvedType);
        assertThrows(UnsolvedSymbolException.class, call::resolve);
    }

    @ParameterizedTest
    @ValueSource(strings = {"1, 2", "new Integer[] {1, 2}"})
    void captureAcceptsExpandedAndArrayVarargs(String arguments) {
        MethodCallExpr call = findCall(
                superWildcardCode(
                        "static <T extends Number> Box<T> pick(Box<T> xs) { return xs; }",
                        "Box<? super Integer> xs",
                        "Example.pick(xs).accept(" + arguments + ")"),
                "accept");
        assertEquals("void", call.calculateResolvedType().describe());
        assertEquals("accept", call.resolve().getName());
    }

    private static String superWildcardCode(String method, String parameters, String expression) {
        return "import java.util.*; class Example { static class Numbers<X extends Number> extends ArrayList<X> {} "
                + "static class Pair<A,B> {} static class Single<B> extends Pair<String,B> {} "
                + "static class Flip<A,B> extends Pair<B,A> {} static class Box<X extends Number> { void accept(X... values) {} } "
                + method + " void test(" + parameters + ") { " + expression + "; } }";
    }

    // Captured containers, write safety, overload selection, and incompatible bounds.
    @ParameterizedTest(name = "{0}")
    @MethodSource("captureRegressionCases")
    void preservesCaptureConstraints(String name, String source, String expected) {
        MethodCallExpr call = parse(source)
                .findFirst(MethodDeclaration.class, m -> m.getNameAsString().equals("test"))
                .get()
                .getBody()
                .get()
                .getStatement(0)
                .asExpressionStmt()
                .getExpression()
                .asMethodCallExpr();
        if (expected.equals("ERROR")) {
            assertThrows(UnsolvedSymbolException.class, call::calculateResolvedType);
            // Declaration resolution alone does not perform method type inference.
            if (!call.getNameAsString().equals("pick")) {
                assertThrows(UnsolvedSymbolException.class, call::resolve);
            }
        } else {
            assertEquals(expected, call.calculateResolvedType().describe());
            assertEquals(call.getNameAsString(), call.resolve().getName());
        }
    }

    // Expected outcomes verified with javac --release 8; no assignment target typing.
    private static Stream<Arguments> captureRegressionCases() {
        return Stream.of(
                Arguments.of(
                        "addall-Integer",
                        "import java.util.*; class Example { static <T> List<T> pick(List<T> xs) { return xs; } void test(List<? super Integer> xs, List<Integer> ys) { Example.pick(xs).addAll(ys); }}",
                        "boolean"),
                Arguments.of(
                        "addall-Number",
                        "import java.util.*; class Example { static <T> List<T> pick(List<T> xs) { return xs; } void test(List<? super Integer> xs, List<Number> ys) { Example.pick(xs).addAll(ys); }}",
                        "ERROR"),
                Arguments.of(
                        "addall-Object",
                        "import java.util.*; class Example { static <T> List<T> pick(List<T> xs) { return xs; } void test(List<? super Integer> xs, List<Object> ys) { Example.pick(xs).addAll(ys); }}",
                        "ERROR"),
                Arguments.of(
                        "addall-extends-Integer",
                        "import java.util.*; class Example { static <T> List<T> pick(List<T> xs) { return xs; } void test(List<? super Integer> xs, List<? extends Integer> ys) { Example.pick(xs).addAll(ys); }}",
                        "boolean"),
                Arguments.of(
                        "addall-super-Integer",
                        "import java.util.*; class Example { static <T> List<T> pick(List<T> xs) { return xs; } void test(List<? super Integer> xs, List<? super Integer> ys) { Example.pick(xs).addAll(ys); }}",
                        "ERROR"),
                Arguments.of(
                        "container-exact-Integer",
                        "import java.util.*; class Example { static class Box<X extends Number> { void accept(List<X> ys) {} } static <T extends Number> Box<T> pick(Box<T> xs) {return xs;} void test(Box<? super Integer> xs, List<Integer> ys) { Example.pick(xs).accept(ys); }}",
                        "ERROR"),
                Arguments.of(
                        "container-exact-Number",
                        "import java.util.*; class Example { static class Box<X extends Number> { void accept(List<X> ys) {} } static <T extends Number> Box<T> pick(Box<T> xs) {return xs;} void test(Box<? super Integer> xs, List<Number> ys) { Example.pick(xs).accept(ys); }}",
                        "ERROR"),
                Arguments.of(
                        "container-exact-Object",
                        "import java.util.*; class Example { static class Box<X extends Number> { void accept(List<X> ys) {} } static <T extends Number> Box<T> pick(Box<T> xs) {return xs;} void test(Box<? super Integer> xs, List<Object> ys) { Example.pick(xs).accept(ys); }}",
                        "ERROR"),
                Arguments.of(
                        "container-exact-extends-Integer",
                        "import java.util.*; class Example { static class Box<X extends Number> { void accept(List<X> ys) {} } static <T extends Number> Box<T> pick(Box<T> xs) {return xs;} void test(Box<? super Integer> xs, List<? extends Integer> ys) { Example.pick(xs).accept(ys); }}",
                        "ERROR"),
                Arguments.of(
                        "container-exact-super-Integer",
                        "import java.util.*; class Example { static class Box<X extends Number> { void accept(List<X> ys) {} } static <T extends Number> Box<T> pick(Box<T> xs) {return xs;} void test(Box<? super Integer> xs, List<? super Integer> ys) { Example.pick(xs).accept(ys); }}",
                        "ERROR"),
                Arguments.of(
                        "container-extends-Integer",
                        "import java.util.*; class Example { static class Box<X extends Number> { void accept(List<? extends X> ys) {} } static <T extends Number> Box<T> pick(Box<T> xs) {return xs;} void test(Box<? super Integer> xs, List<Integer> ys) { Example.pick(xs).accept(ys); }}",
                        "void"),
                Arguments.of(
                        "container-extends-Number",
                        "import java.util.*; class Example { static class Box<X extends Number> { void accept(List<? extends X> ys) {} } static <T extends Number> Box<T> pick(Box<T> xs) {return xs;} void test(Box<? super Integer> xs, List<Number> ys) { Example.pick(xs).accept(ys); }}",
                        "ERROR"),
                Arguments.of(
                        "container-extends-Object",
                        "import java.util.*; class Example { static class Box<X extends Number> { void accept(List<? extends X> ys) {} } static <T extends Number> Box<T> pick(Box<T> xs) {return xs;} void test(Box<? super Integer> xs, List<Object> ys) { Example.pick(xs).accept(ys); }}",
                        "ERROR"),
                Arguments.of(
                        "container-extends-extends-Integer",
                        "import java.util.*; class Example { static class Box<X extends Number> { void accept(List<? extends X> ys) {} } static <T extends Number> Box<T> pick(Box<T> xs) {return xs;} void test(Box<? super Integer> xs, List<? extends Integer> ys) { Example.pick(xs).accept(ys); }}",
                        "void"),
                Arguments.of(
                        "container-extends-super-Integer",
                        "import java.util.*; class Example { static class Box<X extends Number> { void accept(List<? extends X> ys) {} } static <T extends Number> Box<T> pick(Box<T> xs) {return xs;} void test(Box<? super Integer> xs, List<? super Integer> ys) { Example.pick(xs).accept(ys); }}",
                        "ERROR"),
                Arguments.of(
                        "container-super-Integer",
                        "import java.util.*; class Example { static class Box<X extends Number> { void accept(List<? super X> ys) {} } static <T extends Number> Box<T> pick(Box<T> xs) {return xs;} void test(Box<? super Integer> xs, List<Integer> ys) { Example.pick(xs).accept(ys); }}",
                        "ERROR"),
                Arguments.of(
                        "container-super-Number",
                        "import java.util.*; class Example { static class Box<X extends Number> { void accept(List<? super X> ys) {} } static <T extends Number> Box<T> pick(Box<T> xs) {return xs;} void test(Box<? super Integer> xs, List<Number> ys) { Example.pick(xs).accept(ys); }}",
                        "void"),
                Arguments.of(
                        "container-super-Object",
                        "import java.util.*; class Example { static class Box<X extends Number> { void accept(List<? super X> ys) {} } static <T extends Number> Box<T> pick(Box<T> xs) {return xs;} void test(Box<? super Integer> xs, List<Object> ys) { Example.pick(xs).accept(ys); }}",
                        "void"),
                Arguments.of(
                        "container-super-extends-Integer",
                        "import java.util.*; class Example { static class Box<X extends Number> { void accept(List<? super X> ys) {} } static <T extends Number> Box<T> pick(Box<T> xs) {return xs;} void test(Box<? super Integer> xs, List<? extends Integer> ys) { Example.pick(xs).accept(ys); }}",
                        "ERROR"),
                Arguments.of(
                        "container-super-super-Integer",
                        "import java.util.*; class Example { static class Box<X extends Number> { void accept(List<? super X> ys) {} } static <T extends Number> Box<T> pick(Box<T> xs) {return xs;} void test(Box<? super Integer> xs, List<? super Integer> ys) { Example.pick(xs).accept(ys); }}",
                        "ERROR"),
                Arguments.of(
                        "captured varargs null",
                        "import java.util.*; class Example { static class Box<X extends Number> { void accept(X... ys) {} } static <T extends Number> Box<T> pick(Box<T> xs) {return xs;} void test(Box<? super Integer> xs) { Example.pick(xs).accept(null); }}",
                        "void"),
                Arguments.of(
                        "captured varargs integer",
                        "import java.util.*; class Example { static class Box<X extends Number> { void accept(X... ys) {} } static <T extends Number> Box<T> pick(Box<T> xs) {return xs;} void test(Box<? super Integer> xs) { Example.pick(xs).accept(1); }}",
                        "void"),
                Arguments.of(
                        "captured varargs incompatible double",
                        "import java.util.*; class Example { static class Box<X extends Number> { void accept(X... ys) {} } static <T extends Number> Box<T> pick(Box<T> xs) {return xs;} void test(Box<? super Integer> xs) { Example.pick(xs).accept(1.5); }}",
                        "ERROR"),
                Arguments.of(
                        "captured varargs incompatible Number array",
                        "import java.util.*; class Example { static class Box<X extends Number> { void accept(X... ys) {} } static <T extends Number> Box<T> pick(Box<T> xs) {return xs;} void test(Box<? super Integer> xs) { Example.pick(xs).accept(new Number[0]); }}",
                        "ERROR"),
                Arguments.of(
                        "capture overload accepts Integer",
                        "import java.util.*; class Example { static class Box<X extends Number> { Integer accept(X x){return null;} String accept(Object x){return null;} } static <T extends Number> Box<T> pick(Box<T> xs){return xs;} void test(Box<? super Integer> xs) { Example.pick(xs).accept(1); }}",
                        "java.lang.Integer"),
                Arguments.of(
                        "Object overload accepts Double",
                        "import java.util.*; class Example { static class Box<X extends Number> { Integer accept(X x){return null;} String accept(Object x){return null;} } static <T extends Number> Box<T> pick(Box<T> xs){return xs;} void test(Box<? super Integer> xs) { Example.pick(xs).accept(1.5); }}",
                        "java.lang.String"),
                Arguments.of(
                        "Object overload accepts Object",
                        "import java.util.*; class Example { static class Box<X extends Number> { Integer accept(X x){return null;} String accept(Object x){return null;} } static <T extends Number> Box<T> pick(Box<T> xs){return xs;} void test(Box<? super Integer> xs) { Example.pick(xs).accept(new Object()); }}",
                        "java.lang.String"),
                Arguments.of(
                        "Object overload accepts String",
                        "import java.util.*; class Example { static class Box<X extends Number> { Integer accept(X x){return null;} String accept(Object x){return null;} } static <T extends Number> Box<T> pick(Box<T> xs){return xs;} void test(Box<? super Integer> xs) { Example.pick(xs).accept(\"s\"); }}",
                        "java.lang.String"),
                Arguments.of(
                        "instance super formal with concrete argument",
                        "import java.util.*; class Example { <T> T pick(List<? super T> xs){return null;} void test(List<String> xs) { new Example().pick(xs).length(); }}",
                        "int"),
                Arguments.of(
                        "instance super formal with captured argument",
                        "import java.util.*; class Example { <T> T pick(List<? super T> xs){return null;} void test(List<? super String> xs) { new Example().pick(xs).length(); }}",
                        "ERROR"),
                Arguments.of(
                        "reject value outside capture upper bound",
                        "import java.util.*; class Example { static <T> T pick(T value, List<? super T> xs){return null;} void test(List<? super Integer> xs) { Example.pick(\"s\", xs); }}",
                        "ERROR"),
                Arguments.of(
                        "accept value inside capture upper bound",
                        "import java.util.*; class Example { static <T> T pick(T value, List<? super T> xs){return null;} void test(List<? super Integer> xs) { Example.pick(1, xs); }}",
                        "java.lang.Integer"),
                Arguments.of(
                        "reject incompatible invariant arguments",
                        "import java.util.*; class Example { static <T> T pick(List<T> a, List<T> b){return null;} void test(List<String> a, List<Integer> b) { Example.pick(a,b); }}",
                        "ERROR"),
                Arguments.of(
                        "reject incompatible invariant arguments reversed",
                        "import java.util.*; class Example { static <T> T pick(List<T> a, List<T> b){return null;} void test(List<String> a, List<Integer> b) { Example.pick(b,a); }}",
                        "ERROR"),
                Arguments.of(
                        "reject value outside declared Number bound",
                        "import java.util.*; class Example { static <T extends Number> T pick(T a, List<? super T> b){return null;} void test(List<Object> b) { Example.pick(\"s\",b); }}",
                        "ERROR"),
                Arguments.of(
                        "reject unrelated reference array upper bounds",
                        "import java.util.*; class Example { static <T> T pick(List<? super T> a, List<? super T> b){return null;} void test(List<String[]> a, List<Integer[]> b) { Example.pick(a,b); }}",
                        "ERROR"),
                Arguments.of(
                        "overload-nested-invariant",
                        "import java.util.*; class Example { static class Box<X extends Number> { Integer accept(List<X> x){return null;} String accept(Collection<Integer> x){return null;} } static <T extends Number> Box<T> pick(Box<T> xs){return xs;} void test(Box<? super Integer> xs, List<Integer> ys){Example.pick(xs).accept(ys);} }",
                        "java.lang.String"),
                Arguments.of(
                        "overload-super-overload",
                        "import java.util.*; class Example { static class Box<X extends Number> { Integer accept(List<? super X> x){return null;} String accept(Collection<Integer> x){return null;} } static <T extends Number> Box<T> pick(Box<T> xs){return xs;} void test(Box<? super Integer> xs, List<Integer> ys){Example.pick(xs).accept(ys);} }",
                        "java.lang.String"),
                Arguments.of(
                        "overload-extends-overload",
                        "import java.util.*; class Example { static class Box<X extends Number> { Integer accept(List<? extends X> x){return null;} String accept(Collection<Number> x){return null;} } static <T extends Number> Box<T> pick(Box<T> xs){return xs;} void test(Box<? super Integer> xs, List<Number> ys){Example.pick(xs).accept(ys);} }",
                        "java.lang.String"),
                Arguments.of(
                        "array-upper-0",
                        "import java.util.*; class Example { static <T> T pick(List<? super T> a,List<? super T> b){return null;} void test(List<String[]> a,List<Object[]> b){Example.pick(a,b);}}",
                        "java.lang.String[]"),
                Arguments.of(
                        "array-upper-1",
                        "import java.util.*; class Example { static <T> T pick(List<? super T> a,List<? super T> b){return null;} void test(List<int[]> a,List<long[]> b){Example.pick(a,b);}}",
                        "ERROR"),
                Arguments.of(
                        "array-upper-2",
                        "import java.util.*; class Example { static <T> T pick(List<? super T> a,List<? super T> b){return null;} void test(List<CharSequence[]> a,List<java.io.Serializable[]> b){Example.pick(a,b);}}",
                        "ERROR"),
                Arguments.of(
                        "array-upper-3",
                        "import java.util.*; class Example { static <T> T pick(List<? super T> a,List<? super T> b){return null;} void test(List<Number[]> a,List<Runnable[]> b){Example.pick(a,b);}}",
                        "ERROR"),
                Arguments.of(
                        "array-upper-4",
                        "import java.util.*; class Example { static <T> T pick(List<? super T> a,List<? super T> b){return null;} void test(List<String[]> a,List<java.io.Serializable> b){Example.pick(a,b);}}",
                        "java.lang.String[]"),
                Arguments.of(
                        "array-upper-5",
                        "import java.util.*; class Example { static <T> T pick(List<? super T> a,List<? super T> b){return null;} void test(List<String[]> a,List<Runnable> b){Example.pick(a,b);}}",
                        "ERROR"));
    }

    private MethodCallExpr findCall(String source, String methodName) {
        return findCall(parse(source), methodName);
    }

    @ParameterizedTest(name = "{0}")
    @MethodSource("scopedChainedLambdaCases")
    void inferScopedChainedLambda(
            String name, String source, String[] expectedCalls, int expectedArrayLengths, boolean invalid) {
        MethodDeclaration test = parse(source)
                .findFirst(MethodDeclaration.class, method -> method.getNameAsString()
                        .equals("test"))
                .get();
        List<MethodCallExpr> calls = test.getBody().get().findAll(MethodCallExpr.class);
        if (invalid) {
            // The last call deliberately requests a member absent from the inferred type.
            assertTrue(!calls.isEmpty(), name);
            assertThrows(UnsolvedSymbolException.class, calls.get(calls.size() - 1)::calculateResolvedType, name);
            return;
        }
        assertEquals(expectedCalls.length, calls.size(), name);
        for (int i = 0; i < calls.size(); i++) {
            MethodCallExpr call = calls.get(i);
            String[] expected = expectedCalls[i].split("\\|");
            String message = name + ": " + call;
            assertEquals(expected[0], call.getNameAsString(), message);
            assertEquals(expected[1], call.calculateResolvedType().describe().replaceAll(",\\s*", ","), message);
            assertEquals(expected[2], call.resolve().declaringType().getQualifiedName(), message);
        }
        List<FieldAccessExpr> lengths = test.getBody()
                .get()
                .findAll(FieldAccessExpr.class, field -> field.getNameAsString().equals("length"));
        assertEquals(expectedArrayLengths, lengths.size(), name);
        for (FieldAccessExpr length : lengths) {
            assertEquals("int", length.calculateResolvedType().describe(), name);
        }
    }

    // These fixtures were checked against javac --release 8, including their declaring types.
    // Read-only get() chains use the extends-bound view of javac's captured wildcards.
    // Each expected call records its name, return type and declaring type in AST traversal order.
    private static Stream<Arguments> scopedChainedLambdaCases() {
        return Stream.of(
                Arguments.of(
                        "round1: lambda-0-1",
                        "import java.util.*; import java.util.function.*; class Example { static abstract class Mono<T> { static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} }   void test(){Mono.defer(() -> { return (Mono<String>) null; }).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round1: lambda-0-2",
                        "import java.util.*; import java.util.function.*; class Example { static abstract class Mono<T> { static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} }   void test(){Mono.defer((() -> (Mono<String>) null)).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round1: lambda-0-3",
                        "import java.util.*; import java.util.function.*; class Example { static abstract class Mono<T> { static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} }   void test(){Mono.defer(() -> ((Mono<String>) null)).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round1: supplier-0-1",
                        "import java.util.*; import java.util.function.*; class Example { static abstract class Mono<T> { static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} } static Mono<String> strings(){return null;} static class StringSupplier implements Supplier<Mono<String>>{public Mono<String> get(){return null;}}  void test(Supplier<Mono<String>> supplier){Mono.defer(Example::strings).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round1: supplier-0-2",
                        "import java.util.*; import java.util.function.*; class Example { static abstract class Mono<T> { static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} } static Mono<String> strings(){return null;} static class StringSupplier implements Supplier<Mono<String>>{public Mono<String> get(){return null;}}  void test(Supplier<Mono<String>> supplier){Mono.defer(new StringSupplier()).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round1: subclass-0-0",
                        "import java.util.*; import java.util.function.*; class Example { static abstract class Mono<T> { static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} } static class Single<X> extends Mono<X>{}  void test(){Mono.defer(() -> (Single<String>) null).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round1: subclass-0-1",
                        "import java.util.*; import java.util.function.*; class Example { static abstract class Mono<T> { static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} } static class Flipped<A,B> extends Mono<B>{}  void test(){Mono.defer(() -> (Flipped<Long,String>) null).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round1: subclass-0-2",
                        "import java.util.*; import java.util.function.*; class Example { static abstract class Mono<T> { static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} } static class Fixed extends Mono<String>{}  void test(){Mono.defer(() -> (Fixed) null).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round1: subclass-0-3",
                        "import java.util.*; import java.util.function.*; class Example { static abstract class Mono<T> { static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} } static class Fixed extends Mono<String>{}  void test(){Mono.defer(Fixed::new).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round1: subclass-0-4",
                        "import java.util.*; import java.util.function.*; class Example { static abstract class Mono<T> { static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} } static class Mid<A,B> extends Mono<B>{} static class Leaf<X> extends Mid<Long,X>{}  void test(){Mono.defer(() -> (Leaf<String>) null).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round1: lambda-1-0",
                        "import java.util.*; import java.util.function.*; class Example { static abstract class Mono<T> { static <T> Mono<T> defer(Supplier<? extends Mono<T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} }   void test(){Mono.defer(() -> (Mono<String>) null).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round1: lambda-1-1",
                        "import java.util.*; import java.util.function.*; class Example { static abstract class Mono<T> { static <T> Mono<T> defer(Supplier<? extends Mono<T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} }   void test(){Mono.defer(() -> { return (Mono<String>) null; }).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round1: lambda-1-2",
                        "import java.util.*; import java.util.function.*; class Example { static abstract class Mono<T> { static <T> Mono<T> defer(Supplier<? extends Mono<T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} }   void test(){Mono.defer((() -> (Mono<String>) null)).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round1: lambda-1-3",
                        "import java.util.*; import java.util.function.*; class Example { static abstract class Mono<T> { static <T> Mono<T> defer(Supplier<? extends Mono<T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} }   void test(){Mono.defer(() -> ((Mono<String>) null)).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round1: supplier-1-1",
                        "import java.util.*; import java.util.function.*; class Example { static abstract class Mono<T> { static <T> Mono<T> defer(Supplier<? extends Mono<T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} } static Mono<String> strings(){return null;} static class StringSupplier implements Supplier<Mono<String>>{public Mono<String> get(){return null;}}  void test(Supplier<Mono<String>> supplier){Mono.defer(Example::strings).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round1: supplier-1-2",
                        "import java.util.*; import java.util.function.*; class Example { static abstract class Mono<T> { static <T> Mono<T> defer(Supplier<? extends Mono<T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} } static Mono<String> strings(){return null;} static class StringSupplier implements Supplier<Mono<String>>{public Mono<String> get(){return null;}}  void test(Supplier<Mono<String>> supplier){Mono.defer(new StringSupplier()).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round1: subclass-1-0",
                        "import java.util.*; import java.util.function.*; class Example { static abstract class Mono<T> { static <T> Mono<T> defer(Supplier<? extends Mono<T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} } static class Single<X> extends Mono<X>{}  void test(){Mono.defer(() -> (Single<String>) null).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round1: subclass-1-1",
                        "import java.util.*; import java.util.function.*; class Example { static abstract class Mono<T> { static <T> Mono<T> defer(Supplier<? extends Mono<T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} } static class Flipped<A,B> extends Mono<B>{}  void test(){Mono.defer(() -> (Flipped<Long,String>) null).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round1: subclass-1-2",
                        "import java.util.*; import java.util.function.*; class Example { static abstract class Mono<T> { static <T> Mono<T> defer(Supplier<? extends Mono<T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} } static class Fixed extends Mono<String>{}  void test(){Mono.defer(() -> (Fixed) null).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round1: subclass-1-3",
                        "import java.util.*; import java.util.function.*; class Example { static abstract class Mono<T> { static <T> Mono<T> defer(Supplier<? extends Mono<T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} } static class Fixed extends Mono<String>{}  void test(){Mono.defer(Fixed::new).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round1: subclass-1-4",
                        "import java.util.*; import java.util.function.*; class Example { static abstract class Mono<T> { static <T> Mono<T> defer(Supplier<? extends Mono<T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} } static class Mid<A,B> extends Mono<B>{} static class Leaf<X> extends Mid<Long,X>{}  void test(){Mono.defer(() -> (Leaf<String>) null).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round1: lambda-2-1",
                        "import java.util.*; import java.util.function.*; class Example { static abstract class Mono<T> { static <T> Mono<T> defer(Supplier<Mono<T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} }   void test(){Mono.defer(() -> { return (Mono<String>) null; }).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round1: lambda-2-2",
                        "import java.util.*; import java.util.function.*; class Example { static abstract class Mono<T> { static <T> Mono<T> defer(Supplier<Mono<T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} }   void test(){Mono.defer((() -> (Mono<String>) null)).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round1: lambda-2-3",
                        "import java.util.*; import java.util.function.*; class Example { static abstract class Mono<T> { static <T> Mono<T> defer(Supplier<Mono<T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} }   void test(){Mono.defer(() -> ((Mono<String>) null)).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round1: supplier-2-0",
                        "import java.util.*; import java.util.function.*; class Example { static abstract class Mono<T> { static <T> Mono<T> defer(Supplier<Mono<T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} } static Mono<String> strings(){return null;} static class StringSupplier implements Supplier<Mono<String>>{public Mono<String> get(){return null;}}  void test(Supplier<Mono<String>> supplier){Mono.defer(supplier).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round1: supplier-2-1",
                        "import java.util.*; import java.util.function.*; class Example { static abstract class Mono<T> { static <T> Mono<T> defer(Supplier<Mono<T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} } static Mono<String> strings(){return null;} static class StringSupplier implements Supplier<Mono<String>>{public Mono<String> get(){return null;}}  void test(Supplier<Mono<String>> supplier){Mono.defer(Example::strings).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round1: supplier-2-2",
                        "import java.util.*; import java.util.function.*; class Example { static abstract class Mono<T> { static <T> Mono<T> defer(Supplier<Mono<T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} } static Mono<String> strings(){return null;} static class StringSupplier implements Supplier<Mono<String>>{public Mono<String> get(){return null;}}  void test(Supplier<Mono<String>> supplier){Mono.defer(new StringSupplier()).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round1: subclass-2-0",
                        "import java.util.*; import java.util.function.*; class Example { static abstract class Mono<T> { static <T> Mono<T> defer(Supplier<Mono<T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} } static class Single<X> extends Mono<X>{}  void test(){Mono.defer(() -> (Single<String>) null).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round1: subclass-2-1",
                        "import java.util.*; import java.util.function.*; class Example { static abstract class Mono<T> { static <T> Mono<T> defer(Supplier<Mono<T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} } static class Flipped<A,B> extends Mono<B>{}  void test(){Mono.defer(() -> (Flipped<Long,String>) null).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round1: subclass-2-2",
                        "import java.util.*; import java.util.function.*; class Example { static abstract class Mono<T> { static <T> Mono<T> defer(Supplier<Mono<T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} } static class Fixed extends Mono<String>{}  void test(){Mono.defer(() -> (Fixed) null).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round1: subclass-2-3",
                        "import java.util.*; import java.util.function.*; class Example { static abstract class Mono<T> { static <T> Mono<T> defer(Supplier<Mono<T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} } static class Fixed extends Mono<String>{}  void test(){Mono.defer(Fixed::new).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round1: subclass-2-4",
                        "import java.util.*; import java.util.function.*; class Example { static abstract class Mono<T> { static <T> Mono<T> defer(Supplier<Mono<T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} } static class Mid<A,B> extends Mono<B>{} static class Leaf<X> extends Mid<Long,X>{}  void test(){Mono.defer(() -> (Leaf<String>) null).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round1: element-0",
                        "import java.util.*; import java.util.function.*; class Example { static abstract class Mono<T> { static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} }   void test(){Mono.defer(() -> (Mono<Integer>) null).consume(s -> s.intValue());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.Integer>|Example.Mono",
                            "intValue|int|java.lang.Integer"
                        },
                        0,
                        false),
                Arguments.of(
                        "round1: element-1",
                        "import java.util.*; import java.util.function.*; class Example { static abstract class Mono<T> { static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} }   void test(){Mono.defer(() -> (Mono<CharSequence>) null).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.CharSequence>|Example.Mono",
                            "length|int|java.lang.CharSequence"
                        },
                        0,
                        false),
                Arguments.of(
                        "round1: element-2",
                        "import java.util.*; import java.util.function.*; class Example { static abstract class Mono<T> { static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} }   void test(){Mono.defer(() -> (Mono<List<String>>) null).consume(s -> s.get(0).length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.util.List<java.lang.String>>|Example.Mono",
                            "length|int|java.lang.String",
                            "get|java.lang.String|java.util.List"
                        },
                        0,
                        false),
                Arguments.of(
                        "round1: element-3",
                        "import java.util.*; import java.util.function.*; class Example { static abstract class Mono<T> { static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} }   void test(){Mono.defer(() -> (Mono<Map<String,Integer>>) null).consume(s -> s.get(\"x\").intValue());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.util.Map<java.lang.String,java.lang.Integer>>|Example.Mono",
                            "intValue|int|java.lang.Integer",
                            "get|java.lang.Integer|java.util.Map"
                        },
                        0,
                        false),
                Arguments.of(
                        "round1: caller-variable",
                        "import java.util.*; import java.util.function.*; class Example { static abstract class Mono<T> { static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} }  <U extends CharSequence> void test(){Mono.defer(() -> (Mono<U>) null).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<U>|Example.Mono",
                            "length|int|java.lang.CharSequence"
                        },
                        0,
                        false),
                Arguments.of(
                        "round1: map-chain-0",
                        "import java.util.*; import java.util.function.*; class Example { static abstract class Mono<T> { static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} }   void test(){Mono.defer(() -> (Mono<String>) null).map(s -> s.length()).consume(n -> n.intValue());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "map|Example.Mono<java.lang.Integer>|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String",
                            "intValue|int|java.lang.Integer"
                        },
                        0,
                        false),
                Arguments.of(
                        "round1: map-chain-1",
                        "import java.util.*; import java.util.function.*; class Example { static abstract class Mono<T> { static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} }   void test(){Mono.defer(() -> (Mono<String>) null).map(s -> s.substring(1)).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "map|Example.Mono<java.lang.String>|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "substring|java.lang.String|java.lang.String",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round1: map-chain-2",
                        "import java.util.*; import java.util.function.*; class Example { static abstract class Mono<T> { static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} }   void test(){Mono.defer(() -> (Mono<List<String>>) null).map(s -> s.get(0)).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "map|Example.Mono<java.lang.String>|Example.Mono",
                            "defer|Example.Mono<java.util.List<java.lang.String>>|Example.Mono",
                            "get|java.lang.String|java.util.List",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round2: caller-composite-0-lambda",
                        "import java.util.*; import java.util.function.*; class Example {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} }  <U extends CharSequence> void test(){Mono.defer(() -> (Mono<List<U>>)null).consume(s -> s.get(0).length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.util.List<U>>|Example.Mono",
                            "length|int|java.lang.CharSequence",
                            "get|U|java.util.List"
                        },
                        0,
                        false),
                Arguments.of(
                        "round2: caller-composite-0-variable",
                        "import java.util.*; import java.util.function.*; class Example {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} }  <U extends CharSequence> void test(Supplier<Mono<List<U>>> xs){Mono.defer(xs).consume(s -> s.get(0).length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.util.List<U>>|Example.Mono",
                            "length|int|java.lang.CharSequence",
                            "get|U|java.util.List"
                        },
                        0,
                        false),
                Arguments.of(
                        "round2: caller-composite-1-lambda",
                        "import java.util.*; import java.util.function.*; class Example {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} }  <U extends CharSequence> void test(){Mono.defer(() -> (Mono<Map<String,U>>)null).consume(s -> s.get(\"x\").length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.util.Map<java.lang.String,U>>|Example.Mono",
                            "length|int|java.lang.CharSequence",
                            "get|U|java.util.Map"
                        },
                        0,
                        false),
                Arguments.of(
                        "round2: caller-composite-1-variable",
                        "import java.util.*; import java.util.function.*; class Example {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} }  <U extends CharSequence> void test(Supplier<Mono<Map<String,U>>> xs){Mono.defer(xs).consume(s -> s.get(\"x\").length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.util.Map<java.lang.String,U>>|Example.Mono",
                            "length|int|java.lang.CharSequence",
                            "get|U|java.util.Map"
                        },
                        0,
                        false),
                Arguments.of(
                        "round2: caller-composite-2-lambda",
                        "import java.util.*; import java.util.function.*; class Example {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} }  <U extends CharSequence> void test(){Mono.defer(() -> (Mono<U[]>)null).consume(s -> {int length=s.length;});} }",
                        new String[] {"consume|void|Example.Mono", "defer|Example.Mono<U[]>|Example.Mono"},
                        1,
                        false),
                Arguments.of(
                        "round2: caller-composite-2-variable",
                        "import java.util.*; import java.util.function.*; class Example {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} }  <U extends CharSequence> void test(Supplier<Mono<U[]>> xs){Mono.defer(xs).consume(s -> {int length=s.length;});} }",
                        new String[] {"consume|void|Example.Mono", "defer|Example.Mono<U[]>|Example.Mono"},
                        1,
                        false),
                Arguments.of(
                        "round2: caller-composite-3-lambda",
                        "import java.util.*; import java.util.function.*; class Example {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} }  <U extends CharSequence> void test(){Mono.defer(() -> (Mono<List<? extends U>>)null).consume(s -> s.get(0).length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.util.List<? extends U>>|Example.Mono",
                            "length|int|java.lang.CharSequence",
                            "get|? extends U|java.util.List"
                        },
                        0,
                        false),
                Arguments.of(
                        "round2: caller-composite-3-variable",
                        "import java.util.*; import java.util.function.*; class Example {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} }  <U extends CharSequence> void test(Supplier<Mono<List<? extends U>>> xs){Mono.defer(xs).consume(s -> s.get(0).length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.util.List<? extends U>>|Example.Mono",
                            "length|int|java.lang.CharSequence",
                            "get|? extends U|java.util.List"
                        },
                        0,
                        false),
                Arguments.of(
                        "round2: array-0-lambda",
                        "import java.util.*; import java.util.function.*; class Example {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} }   void test(){Mono.defer(() -> (Mono<String[]>)null).consume(s -> {int length=s.length;});} }",
                        new String[] {"consume|void|Example.Mono", "defer|Example.Mono<java.lang.String[]>|Example.Mono"
                        },
                        1,
                        false),
                Arguments.of(
                        "round2: array-0-variable",
                        "import java.util.*; import java.util.function.*; class Example {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} }   void test(Supplier<Mono<String[]>> xs){Mono.defer(xs).consume(s -> {int length=s.length;});} }",
                        new String[] {"consume|void|Example.Mono", "defer|Example.Mono<java.lang.String[]>|Example.Mono"
                        },
                        1,
                        false),
                Arguments.of(
                        "round2: array-1-lambda",
                        "import java.util.*; import java.util.function.*; class Example {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} }   void test(){Mono.defer(() -> (Mono<int[]>)null).consume(s -> {int length=s.length;});} }",
                        new String[] {"consume|void|Example.Mono", "defer|Example.Mono<int[]>|Example.Mono"},
                        1,
                        false),
                Arguments.of(
                        "round2: array-1-variable",
                        "import java.util.*; import java.util.function.*; class Example {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} }   void test(Supplier<Mono<int[]>> xs){Mono.defer(xs).consume(s -> {int length=s.length;});} }",
                        new String[] {"consume|void|Example.Mono", "defer|Example.Mono<int[]>|Example.Mono"},
                        1,
                        false),
                Arguments.of(
                        "round2: array-2-lambda",
                        "import java.util.*; import java.util.function.*; class Example {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} }   void test(){Mono.defer(() -> (Mono<String[][]>)null).consume(s -> {int length=s.length;});} }",
                        new String[] {
                            "consume|void|Example.Mono", "defer|Example.Mono<java.lang.String[][]>|Example.Mono"
                        },
                        1,
                        false),
                Arguments.of(
                        "round2: array-2-variable",
                        "import java.util.*; import java.util.function.*; class Example {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} }   void test(Supplier<Mono<String[][]>> xs){Mono.defer(xs).consume(s -> {int length=s.length;});} }",
                        new String[] {
                            "consume|void|Example.Mono", "defer|Example.Mono<java.lang.String[][]>|Example.Mono"
                        },
                        1,
                        false),
                Arguments.of(
                        "round2: caller-ground-0",
                        "import java.util.*; import java.util.function.*; class Example {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} }  <U extends CharSequence> void test(){Mono.defer(() -> (Mono<U>)null).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<U>|Example.Mono",
                            "length|int|java.lang.CharSequence"
                        },
                        0,
                        false),
                Arguments.of(
                        "round2: caller-ground-1",
                        "import java.util.*; import java.util.function.*; class Example {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} }  <U extends CharSequence> void test(){Mono.defer(() -> (Mono<U>)null).consume((U s) -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<U>|Example.Mono",
                            "length|int|java.lang.CharSequence"
                        },
                        0,
                        false),
                Arguments.of(
                        "round2: caller-ground-2",
                        "import java.util.*; import java.util.function.*; class Example {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} }  <U extends CharSequence> void test(){Mono.defer(() -> (Mono<U>)null).consume(s -> {s.length();});} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<U>|Example.Mono",
                            "length|int|java.lang.CharSequence"
                        },
                        0,
                        false),
                Arguments.of(
                        "round2: caller-intersection",
                        "import java.util.*; import java.util.function.*; class Example {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} }  <U extends Number & CharSequence> void test(){Mono.defer(() -> (Mono<U>)null).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<U>|Example.Mono",
                            "length|int|java.lang.CharSequence"
                        },
                        0,
                        false),
                Arguments.of(
                        "round2: supplier-projection-0",
                        "import java.util.*; import java.util.function.*; class Example {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} } static class Swapped<A,B> implements Supplier<Mono<B>>{public Mono<B> get(){return null;}}  void test(Swapped<Long,String> xs){Mono.defer(xs).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round2: supplier-projection-1",
                        "import java.util.*; import java.util.function.*; class Example {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} } static class Parent<A,B> implements Supplier<Mono<B>>{public Mono<B> get(){return null;}} static class Leaf<X> extends Parent<Long,X>{}  void test(Leaf<String> xs){Mono.defer(xs).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round2: supplier-projection-2",
                        "import java.util.*; import java.util.function.*; class Example {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} } static class Fixed implements Supplier<Mono<String>>{public Mono<String> get(){return null;}}  void test(Fixed xs){Mono.defer(xs).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round2: supplier-varargs-0",
                        "import java.util.*; import java.util.function.*; class Example {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>>... xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} }   void test(){Mono.defer(() -> (Mono<String>)null).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round2: supplier-varargs-1",
                        "import java.util.*; import java.util.function.*; class Example {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>>... xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} }   void test(){Mono.defer(() -> (Mono<String>)null, () -> (Mono<String>)null).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round2: supplier-varargs-2",
                        "import java.util.*; import java.util.function.*; class Example {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>>... xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} }   void test(Supplier<Mono<String>>[] xs){Mono.defer(xs).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round2: supplier-varargs-3",
                        "import java.util.*; import java.util.function.*; class Example {static abstract class Mono<T>{ static <T> Mono<T> defer(String tag, Supplier<? extends Mono<? extends T>>... xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} }   void test(){Mono.defer(\"tag\", () -> (Mono<String>)null).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round2: supplier-varargs-4",
                        "import java.util.*; import java.util.function.*; class Example {static abstract class Mono<T>{ static <T> Mono<T> defer(String tag, Supplier<? extends Mono<? extends T>>... xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} }   void test(){Mono.defer(\"tag\", () -> (Mono<String>)null, () -> (Mono<String>)null).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round2: supplier-varargs-5",
                        "import java.util.*; import java.util.function.*; class Example {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> first, Supplier<? extends Mono<? extends T>>... xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} }   void test(){Mono.defer(() -> (Mono<String>)null).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round2: supplier-varargs-lub-0",
                        "import java.util.*; import java.util.function.*; class Example {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>>... xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} } static class Base{String name(){return \"\";}} static class Left extends Base{} static class Right extends Base{}  void test(){Mono.defer(() -> (Mono<Base>)null, () -> (Mono<Left>)null).consume(s -> s.name().length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<Example.Base>|Example.Mono",
                            "length|int|java.lang.String",
                            "name|java.lang.String|Example.Base"
                        },
                        0,
                        false),
                Arguments.of(
                        "round2: supplier-varargs-lub-1",
                        "import java.util.*; import java.util.function.*; class Example {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>>... xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} } static class Base{String name(){return \"\";}} static class Left extends Base{} static class Right extends Base{}  void test(){Mono.defer(() -> (Mono<Left>)null, () -> (Mono<Base>)null).consume(s -> s.name().length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<Example.Base>|Example.Mono",
                            "length|int|java.lang.String",
                            "name|java.lang.String|Example.Base"
                        },
                        0,
                        false),
                Arguments.of(
                        "round2: supplier-varargs-lub-2",
                        "import java.util.*; import java.util.function.*; class Example {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>>... xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} } static class Base{String name(){return \"\";}} static class Left extends Base{} static class Right extends Base{}  void test(){Mono.defer(() -> (Mono<Left>)null, () -> (Mono<Right>)null).consume(s -> s.name().length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<Example.Base>|Example.Mono",
                            "length|int|java.lang.String",
                            "name|java.lang.String|Example.Base"
                        },
                        0,
                        false),
                Arguments.of(
                        "round2: map-stage-0",
                        "import java.util.*; import java.util.function.*; class Example {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} } static Mono<String> strings(){return null;}  void test(){Mono.defer(Example::strings).map(s -> s.length()).consume(n -> n.intValue());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "map|Example.Mono<java.lang.Integer>|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String",
                            "intValue|int|java.lang.Integer"
                        },
                        0,
                        false),
                Arguments.of(
                        "round2: map-stage-1",
                        "import java.util.*; import java.util.function.*; class Example {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} }   void test(){Mono.defer(() -> (Mono<String>)null).map(String::length).consume(n -> n.intValue());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "map|Example.Mono<java.lang.Integer>|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "intValue|int|java.lang.Integer"
                        },
                        0,
                        false),
                Arguments.of(
                        "round2: map-stage-2",
                        "import java.util.*; import java.util.function.*; class Example {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} }   void test(){Mono.defer(() -> (Mono<String>)null).map(s -> s.substring(1)).map(s -> s.length()).consume(n -> n.intValue());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "map|Example.Mono<java.lang.Integer>|Example.Mono",
                            "map|Example.Mono<java.lang.String>|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "substring|java.lang.String|java.lang.String",
                            "length|int|java.lang.String",
                            "intValue|int|java.lang.Integer"
                        },
                        0,
                        false),
                Arguments.of(
                        "round2: map-stage-3",
                        "import java.util.*; import java.util.function.*; class Example {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} }  <U extends CharSequence> void test(){Mono.defer(() -> (Mono<List<U>>)null).map(s -> s.get(0)).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "map|Example.Mono<U>|Example.Mono",
                            "defer|Example.Mono<java.util.List<U>>|Example.Mono",
                            "get|U|java.util.List",
                            "length|int|java.lang.CharSequence"
                        },
                        0,
                        false),
                Arguments.of(
                        "round2: inherited-consumer",
                        "import java.util.*; import java.util.function.*; class Example {interface Sink<X>{ default void consume(Consumer<? super X> action){} } static abstract class Mono<T> implements Sink<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;}}   void test(){Mono.defer(() -> (Mono<String>)null).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Sink",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round3: parenthesized-chain",
                        "import java.util.*; import java.util.function.*; class Example{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;}}  void test(){((Mono.defer(() -> (Mono<String>)null))).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round3: explicit-consumer",
                        "import java.util.*; import java.util.function.*; class Example{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;}}  void test(){Mono.defer(() -> (Mono<String>)null).consume((String s) -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round3: returning-void-consumer",
                        "import java.util.*; import java.util.function.*; class Example{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;}}  void test(){Mono.defer(() -> (Mono<String>)null).consume(s -> {s.length(); return;});} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round3: cast-supplier",
                        "import java.util.*; import java.util.function.*; class Example{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;}}  void test(){Mono.defer((Supplier<Mono<String>>) (() -> (Mono<String>)null)).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round3: explicit-supertype",
                        "import java.util.*; import java.util.function.*; class Example{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;}}  void test(){Mono.<CharSequence>defer(() -> (Mono<String>)null).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.CharSequence>|Example.Mono",
                            "length|int|java.lang.CharSequence"
                        },
                        0,
                        false),
                Arguments.of(
                        "round3: caller-name-shadow",
                        "import java.util.*; import java.util.function.*; class Example{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;}} <T extends CharSequence> void test(){Mono.defer(() -> (Mono<T>)null).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<T>|Example.Mono",
                            "length|int|java.lang.CharSequence"
                        },
                        0,
                        false),
                Arguments.of(
                        "round3: caller-class-variable",
                        "import java.util.*; import java.util.function.*; class Example<U extends CharSequence>{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;}}  void test(){Mono.defer(() -> (Mono<U>)null).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<U>|Example.Mono",
                            "length|int|java.lang.CharSequence"
                        },
                        0,
                        false),
                Arguments.of(
                        "round3: caller-two-variables",
                        "import java.util.*; import java.util.function.*; class Example{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;}} <U extends CharSequence,V extends CharSequence> void test(){Mono.defer(() -> (Mono<Map<U,V>>)null).consume(s -> s.get((U)null).length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.util.Map<U,V>>|Example.Mono",
                            "length|int|java.lang.CharSequence",
                            "get|V|java.util.Map"
                        },
                        0,
                        false),
                Arguments.of(
                        "round3: block-two-returns",
                        "import java.util.*; import java.util.function.*; class Example{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;}}  void test(boolean flag){Mono.defer(() -> {if(flag) return (Mono<String>)null; return (Mono<String>)null;}).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round3: block-subclass-return",
                        "import java.util.*; import java.util.function.*; class Example{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;}}static class Fixed extends Mono<String>{}  void test(boolean flag){Mono.defer(() -> {if(flag) return (Mono<String>)null; return (Fixed)null;}).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round3: consumer-variable",
                        "import java.util.*; import java.util.function.*; class Example{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;}}  void test(Consumer<CharSequence> action){Mono.defer(() -> (Mono<String>)null).consume(action);} }",
                        new String[] {"consume|void|Example.Mono", "defer|Example.Mono<java.lang.String>|Example.Mono"},
                        0,
                        false),
                Arguments.of(
                        "round3: mapper-block-return",
                        "import java.util.*; import java.util.function.*; class Example{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;}}  void test(){Mono.defer(() -> (Mono<String>)null).map(s -> {return s.length();}).consume(n -> n.intValue());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "map|Example.Mono<java.lang.Integer>|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String",
                            "intValue|int|java.lang.Integer"
                        },
                        0,
                        false),
                Arguments.of(
                        "round3: local-alias",
                        "import java.util.*; import java.util.function.*; class Example{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;}} <U extends CharSequence> void test(){Mono<U> value=Mono.defer(() -> (Mono<U>)null); value.consume(s -> s.length());} }",
                        new String[] {
                            "defer|Example.Mono<U>|Example.Mono",
                            "consume|void|Example.Mono",
                            "length|int|java.lang.CharSequence"
                        },
                        0,
                        false),
                Arguments.of(
                        "round3: nested-supplier-variable",
                        "import java.util.*; import java.util.function.*; class Example{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;}}  void test(){Supplier<? extends Mono<? extends String>> source=() -> (Mono<String>)null; Mono.defer(source).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round3: callback-string-must-not-be-integer",
                        "import java.util.*; import java.util.function.*; class Example{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;}}  void test(){Mono.defer(() -> (Mono<String>)null).consume(s -> s.intValue());} }",
                        new String[] {},
                        0,
                        true),
                Arguments.of(
                        "round3: callback-integer-must-not-be-string",
                        "import java.util.*; import java.util.function.*; class Example{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;}}  void test(){Mono.defer(() -> (Mono<Integer>)null).consume(s -> s.length());} }",
                        new String[] {},
                        0,
                        true),
                Arguments.of(
                        "round3: mapped-integer-must-not-be-string",
                        "import java.util.*; import java.util.function.*; class Example{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;}}  void test(){Mono.defer(() -> (Mono<String>)null).map(s -> s.length()).consume(s -> s.length());} }",
                        new String[] {},
                        0,
                        true),
                Arguments.of(
                        "round3: array-length-is-not-method",
                        "import java.util.*; import java.util.function.*; class Example{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;}}  void test(){Mono.defer(() -> (Mono<String[]>)null).consume(s -> s.length());} }",
                        new String[] {},
                        0,
                        true),
                Arguments.of(
                        "round4: shadow-number-method",
                        "import java.util.*; import java.util.function.*; class Example{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} Mono<T> tap(Consumer<? super T> fn){return this;}} <T extends Number> void test(){Mono.defer(() -> (Mono<T>)null).consume(s -> s.doubleValue());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<T>|Example.Mono",
                            "doubleValue|double|java.lang.Number"
                        },
                        0,
                        false),
                Arguments.of(
                        "round4: shadow-number-class",
                        "import java.util.*; import java.util.function.*; class Example<T extends Number>{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} Mono<T> tap(Consumer<? super T> fn){return this;}}  void test(){Mono.defer(() -> (Mono<T>)null).consume(s -> s.doubleValue());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<T>|Example.Mono",
                            "doubleValue|double|java.lang.Number"
                        },
                        0,
                        false),
                Arguments.of(
                        "round4: shadow-value-return",
                        "import java.util.*; import java.util.function.*; class Example{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} Mono<T> tap(Consumer<? super T> fn){return this;}} <T extends CharSequence> void test(Mono<T> value){Mono.defer(() -> value).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<T>|Example.Mono",
                            "length|int|java.lang.CharSequence"
                        },
                        0,
                        false),
                Arguments.of(
                        "round4: shadow-supplier-variable",
                        "import java.util.*; import java.util.function.*; class Example{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} Mono<T> tap(Consumer<? super T> fn){return this;}} <T extends CharSequence> void test(Supplier<Mono<T>> source){Mono.defer(source).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<T>|Example.Mono",
                            "length|int|java.lang.CharSequence"
                        },
                        0,
                        false),
                Arguments.of(
                        "round4: shadow-two-variables",
                        "import java.util.*; import java.util.function.*; class Example{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} Mono<T> tap(Consumer<? super T> fn){return this;}} <T extends CharSequence,R extends CharSequence> void test(){Mono.defer(() -> (Mono<Map<T,R>>)null).map(s -> s.get((T)null)).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "map|Example.Mono<R>|Example.Mono",
                            "defer|Example.Mono<java.util.Map<T,R>>|Example.Mono",
                            "get|R|java.util.Map",
                            "length|int|java.lang.CharSequence"
                        },
                        0,
                        false),
                Arguments.of(
                        "round4: caller-interface-member",
                        "import java.util.*; import java.util.function.*; class Example{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} Mono<T> tap(Consumer<? super T> fn){return this;}} <U extends CharSequence> void test(){Mono.defer(() -> (Mono<U>)null).consume(s -> s.subSequence(0,1).length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<U>|Example.Mono",
                            "length|int|java.lang.CharSequence",
                            "subSequence|java.lang.CharSequence|java.lang.CharSequence"
                        },
                        0,
                        false),
                Arguments.of(
                        "round4: mapper-variable",
                        "import java.util.*; import java.util.function.*; class Example{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} Mono<T> tap(Consumer<? super T> fn){return this;}}  void test(Function<CharSequence,Integer> fn){Mono.defer(() -> (Mono<String>)null).map(fn).consume(s -> s.intValue());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "map|Example.Mono<java.lang.Integer>|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "intValue|int|java.lang.Integer"
                        },
                        0,
                        false),
                Arguments.of(
                        "round4: mapper-explicit-input",
                        "import java.util.*; import java.util.function.*; class Example{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} Mono<T> tap(Consumer<? super T> fn){return this;}}  void test(){Mono.defer(() -> (Mono<String>)null).map((CharSequence s) -> s.length()).consume(s -> s.intValue());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "map|Example.Mono<java.lang.Integer>|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.CharSequence",
                            "intValue|int|java.lang.Integer"
                        },
                        0,
                        false),
                Arguments.of(
                        "round4: fixed-prefix-expression",
                        "import java.util.*; import java.util.function.*; class Example{static abstract class Mono<T>{static <T> Mono<T> defer(String tag,Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} Mono<T> tap(Consumer<? super T> fn){return this;}}static String label(){return \"tag\";}  void test(){Mono.defer(label(), () -> (Mono<String>)null).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "label|java.lang.String|Example",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round4: enclosed-array-chain",
                        "import java.util.*; import java.util.function.*; class Example{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} Mono<T> tap(Consumer<? super T> fn){return this;}}  void test(){((Mono.defer(() -> (Mono<int[]>)null))).consume(s -> {int n=s.length;});} }",
                        new String[] {"consume|void|Example.Mono", "defer|Example.Mono<int[]>|Example.Mono"},
                        1,
                        false),
                Arguments.of(
                        "round5: producer-factory-call",
                        "import java.util.*; import java.util.function.*; class Example{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} Mono<T> tap(Consumer<? super T> fn){return this;}}static Mono<String> strings(){return null;}  void test(){Mono.defer(() -> strings()).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "strings|Example.Mono<java.lang.String>|Example",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round5: producer-generic-call",
                        "import java.util.*; import java.util.function.*; class Example{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} Mono<T> tap(Consumer<? super T> fn){return this;}}static <X> Mono<X> wrap(X x){return null;}  void test(){Mono.defer(() -> wrap(\"x\")).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "wrap|Example.Mono<java.lang.String>|Example",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round5: nested-defer-call",
                        "import java.util.*; import java.util.function.*; class Example{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} Mono<T> tap(Consumer<? super T> fn){return this;}}  void test(){Mono.defer(() -> Mono.defer(() -> (Mono<String>)null)).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round5: nested-defer-caller",
                        "import java.util.*; import java.util.function.*; class Example{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} Mono<T> tap(Consumer<? super T> fn){return this;}} <U extends CharSequence> void test(){Mono.defer(() -> Mono.defer(() -> (Mono<U>)null)).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<U>|Example.Mono",
                            "defer|Example.Mono<U>|Example.Mono",
                            "length|int|java.lang.CharSequence"
                        },
                        0,
                        false),
                Arguments.of(
                        "round5: block-supplier-get",
                        "import java.util.*; import java.util.function.*; class Example{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} Mono<T> tap(Consumer<? super T> fn){return this;}} <U extends CharSequence> void test(){Mono.defer(() -> {Supplier<Mono<U>> source=() -> (Mono<U>)null; return source.get();}).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<U>|Example.Mono",
                            "get|Example.Mono<U>|java.util.function.Supplier",
                            "length|int|java.lang.CharSequence"
                        },
                        0,
                        false),
                Arguments.of(
                        "round5: conditional-same-producer",
                        "import java.util.*; import java.util.function.*; class Example{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} Mono<T> tap(Consumer<? super T> fn){return this;}}static class Single<X> extends Mono<X>{} <U extends CharSequence> void test(boolean flag){Mono.defer(() -> flag ? (Mono<U>)null : (Single<U>)null).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<U>|Example.Mono",
                            "length|int|java.lang.CharSequence"
                        },
                        0,
                        false),
                Arguments.of(
                        "round5: tap-consumer-stage",
                        "import java.util.*; import java.util.function.*; class Example{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} Mono<T> tap(Consumer<? super T> fn){return this;}}  void test(){Mono.defer(() -> (Mono<String>)null).tap(s -> s.length()).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "tap|Example.Mono<java.lang.String>|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round5: tap-caller-stage",
                        "import java.util.*; import java.util.function.*; class Example{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} Mono<T> tap(Consumer<? super T> fn){return this;}} <U extends CharSequence> void test(){Mono.defer(() -> (Mono<U>)null).tap(s -> s.length()).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "tap|Example.Mono<U>|Example.Mono",
                            "defer|Example.Mono<U>|Example.Mono",
                            "length|int|java.lang.CharSequence",
                            "length|int|java.lang.CharSequence"
                        },
                        0,
                        false),
                Arguments.of(
                        "round5: deep-caller-map-stages",
                        "import java.util.*; import java.util.function.*; class Example{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} Mono<T> tap(Consumer<? super T> fn){return this;}} <U extends CharSequence> void test(){Mono.defer(() -> (Mono<Map<String,List<U>>>)null).map(s -> s.get(\"x\")).map(s -> s.get(0)).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "map|Example.Mono<U>|Example.Mono",
                            "map|Example.Mono<java.util.List<U>>|Example.Mono",
                            "defer|Example.Mono<java.util.Map<java.lang.String,java.util.List<U>>>|Example.Mono",
                            "get|java.util.List<U>|java.util.Map",
                            "get|U|java.util.List",
                            "length|int|java.lang.CharSequence"
                        },
                        0,
                        false),
                Arguments.of(
                        "round5: mapper-array-length",
                        "import java.util.*; import java.util.function.*; class Example{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} Mono<T> tap(Consumer<? super T> fn){return this;}}  void test(){Mono.defer(() -> (Mono<String[]>)null).map(s -> s.length).consume(s -> s.intValue());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "map|Example.Mono<java.lang.Integer>|Example.Mono",
                            "defer|Example.Mono<java.lang.String[]>|Example.Mono",
                            "intValue|int|java.lang.Integer"
                        },
                        1,
                        false),
                Arguments.of(
                        "round5: conditional-null-producer",
                        "import java.util.*; import java.util.function.*; class Example{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} Mono<T> tap(Consumer<? super T> fn){return this;}}  void test(boolean flag){Mono.defer(() -> flag ? (Mono<String>)null : null).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round5: consumer-reference",
                        "import java.util.*; import java.util.function.*; class Example{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} Mono<T> tap(Consumer<? super T> fn){return this;}}static void read(CharSequence s){}  void test(){Mono.defer(() -> (Mono<String>)null).consume(Example::read);} }",
                        new String[] {"consume|void|Example.Mono", "defer|Example.Mono<java.lang.String>|Example.Mono"},
                        0,
                        false),
                Arguments.of(
                        "round5: independent-string-then-integer",
                        "import java.util.*; import java.util.function.*; class Example{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} Mono<T> tap(Consumer<? super T> fn){return this;}}  void test(){Mono.defer(() -> (Mono<String>)null).consume(s -> s.length()); Mono.defer(() -> (Mono<Integer>)null).consume(s -> s.intValue());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String",
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.Integer>|Example.Mono",
                            "intValue|int|java.lang.Integer"
                        },
                        0,
                        false),
                Arguments.of(
                        "round5: independent-integer-then-string",
                        "import java.util.*; import java.util.function.*; class Example{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;} Mono<T> tap(Consumer<? super T> fn){return this;}}  void test(){Mono.defer(() -> (Mono<Integer>)null).consume(s -> s.intValue()); Mono.defer(() -> (Mono<String>)null).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.Integer>|Example.Mono",
                            "intValue|int|java.lang.Integer",
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.lang.String>|Example.Mono",
                            "length|int|java.lang.String"
                        },
                        0,
                        false),
                Arguments.of(
                        "round6: class-R-and-map-R",
                        "import java.util.*; import java.util.function.*; class Example<R extends CharSequence>{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;}}  void test(){Mono.defer(() -> (Mono<R>)null).map(s -> s.length()).consume(s -> s.intValue());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "map|Example.Mono<java.lang.Integer>|Example.Mono",
                            "defer|Example.Mono<R>|Example.Mono",
                            "length|int|java.lang.CharSequence",
                            "intValue|int|java.lang.Integer"
                        },
                        0,
                        false),
                Arguments.of(
                        "round6: class-T-and-R",
                        "import java.util.*; import java.util.function.*; class Example<T extends Number,R extends CharSequence>{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;}}  void test(){Mono.defer(() -> (Mono<Map<T,R>>)null).map(s -> s.get((T)null)).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "map|Example.Mono<R>|Example.Mono",
                            "defer|Example.Mono<java.util.Map<T,R>>|Example.Mono",
                            "get|R|java.util.Map",
                            "length|int|java.lang.CharSequence"
                        },
                        0,
                        false),
                Arguments.of(
                        "round6: subclass-same-name-T",
                        "import java.util.*; import java.util.function.*; class Example<T extends CharSequence>{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;}}static class Source<T> extends Mono<T>{}  void test(){Mono.defer(() -> (Source<T>)null).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<T>|Example.Mono",
                            "length|int|java.lang.CharSequence"
                        },
                        0,
                        false),
                Arguments.of(
                        "round6: inherited-consumer-same-name-T",
                        "import java.util.*; import java.util.function.*; class Example<T extends CharSequence>{interface Sink<T>{default void consume(Consumer<? super T> fn){}} static abstract class Mono<T> implements Sink<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;}}  void test(){Mono.defer(() -> (Mono<T>)null).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Sink",
                            "defer|Example.Mono<T>|Example.Mono",
                            "length|int|java.lang.CharSequence"
                        },
                        0,
                        false),
                Arguments.of(
                        "round6: supplier-same-name-T",
                        "import java.util.*; import java.util.function.*; class Example<T extends CharSequence>{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;}}static class Source<T> implements Supplier<Mono<T>>{public Mono<T> get(){return null;}}  void test(Source<T> source){Mono.defer(source).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<T>|Example.Mono",
                            "length|int|java.lang.CharSequence"
                        },
                        0,
                        false),
                Arguments.of(
                        "round6: explicit-caller-T",
                        "import java.util.*; import java.util.function.*; class Example{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;}} <T extends CharSequence> void test(){Mono.<T>defer(() -> (Mono<T>)null).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<T>|Example.Mono",
                            "length|int|java.lang.CharSequence"
                        },
                        0,
                        false),
                Arguments.of(
                        "round6: enclosed-caller-T",
                        "import java.util.*; import java.util.function.*; class Example<T extends CharSequence>{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;}}  void test(){((Mono.defer(() -> (Mono<T>)null))).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<T>|Example.Mono",
                            "length|int|java.lang.CharSequence"
                        },
                        0,
                        false),
                Arguments.of(
                        "round6: callback-bound-call",
                        "import java.util.*; import java.util.function.*; class Example<T extends Number>{static abstract class Mono<T>{static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> fn){} <R> Mono<R> map(Function<? super T,? extends R> fn){return null;}}static int read(Number n){return 0;}  void test(){Mono.defer(() -> (Mono<T>)null).consume(s -> read(s));} }",
                        new String[] {
                            "consume|void|Example.Mono", "defer|Example.Mono<T>|Example.Mono", "read|int|Example"
                        },
                        0,
                        false),
                Arguments.of(
                        "round7: bounded-wildcard-0-lambda",
                        "import java.util.*; import java.util.function.*; class Example  {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} } <V extends CharSequence, U extends V> void test(){  Mono.defer(() -> (Mono<List<? extends U>>)null).consume(s -> s.get(0).length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.util.List<? extends U>>|Example.Mono",
                            "length|int|java.lang.CharSequence",
                            "get|? extends U|java.util.List"
                        },
                        0,
                        false),
                Arguments.of(
                        "round7: bounded-wildcard-0-variable",
                        "import java.util.*; import java.util.function.*; class Example  {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} } <V extends CharSequence, U extends V> void test(){ Supplier<Mono<List<? extends U>>> xs=()->null; Mono.defer(xs).consume(s -> s.get(0).length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.util.List<? extends U>>|Example.Mono",
                            "length|int|java.lang.CharSequence",
                            "get|? extends U|java.util.List"
                        },
                        0,
                        false),
                Arguments.of(
                        "round7: bounded-wildcard-1-lambda",
                        "import java.util.*; import java.util.function.*; class Example  {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} } <U extends CharSequence & java.io.Serializable> void test(){  Mono.defer(() -> (Mono<List<? extends U>>)null).consume(s -> s.get(0).length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.util.List<? extends U>>|Example.Mono",
                            "length|int|java.lang.CharSequence",
                            "get|? extends U|java.util.List"
                        },
                        0,
                        false),
                Arguments.of(
                        "round7: bounded-wildcard-1-variable",
                        "import java.util.*; import java.util.function.*; class Example  {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} } <U extends CharSequence & java.io.Serializable> void test(){ Supplier<Mono<List<? extends U>>> xs=()->null; Mono.defer(xs).consume(s -> s.get(0).length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.util.List<? extends U>>|Example.Mono",
                            "length|int|java.lang.CharSequence",
                            "get|? extends U|java.util.List"
                        },
                        0,
                        false),
                Arguments.of(
                        "round7: bounded-wildcard-2-lambda",
                        "import java.util.*; import java.util.function.*; class Example <U extends CharSequence> {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} }  void test(){  Mono.defer(() -> (Mono<List<? extends U>>)null).consume(s -> s.get(0).subSequence(0,1).length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.util.List<? extends U>>|Example.Mono",
                            "length|int|java.lang.CharSequence",
                            "subSequence|java.lang.CharSequence|java.lang.CharSequence",
                            "get|? extends U|java.util.List"
                        },
                        0,
                        false),
                Arguments.of(
                        "round7: bounded-wildcard-2-variable",
                        "import java.util.*; import java.util.function.*; class Example <U extends CharSequence> {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} }  void test(){ Supplier<Mono<List<? extends U>>> xs=()->null; Mono.defer(xs).consume(s -> s.get(0).subSequence(0,1).length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.util.List<? extends U>>|Example.Mono",
                            "length|int|java.lang.CharSequence",
                            "subSequence|java.lang.CharSequence|java.lang.CharSequence",
                            "get|? extends U|java.util.List"
                        },
                        0,
                        false),
                Arguments.of(
                        "round7: bounded-wildcard-3-lambda",
                        "import java.util.*; import java.util.function.*; class Example  {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} } <U extends CharSequence> void test(){  Mono.defer(() -> (Mono<Map<String, ? extends U>>)null).consume(s -> s.get(\"x\").length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.util.Map<java.lang.String,? extends U>>|Example.Mono",
                            "length|int|java.lang.CharSequence",
                            "get|? extends U|java.util.Map"
                        },
                        0,
                        false),
                Arguments.of(
                        "round7: bounded-wildcard-3-variable",
                        "import java.util.*; import java.util.function.*; class Example  {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} } <U extends CharSequence> void test(){ Supplier<Mono<Map<String, ? extends U>>> xs=()->null; Mono.defer(xs).consume(s -> s.get(\"x\").length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.util.Map<java.lang.String,? extends U>>|Example.Mono",
                            "length|int|java.lang.CharSequence",
                            "get|? extends U|java.util.Map"
                        },
                        0,
                        false),
                Arguments.of(
                        "round7: bounded-wildcard-4-lambda",
                        "import java.util.*; import java.util.function.*; class Example  {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} } <U extends CharSequence> void test(){  Mono.defer(() -> (Mono<List<List<? extends U>>>)null).consume(s -> s.get(0).get(0).length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.util.List<java.util.List<? extends U>>>|Example.Mono",
                            "length|int|java.lang.CharSequence",
                            "get|? extends U|java.util.List",
                            "get|java.util.List<? extends U>|java.util.List"
                        },
                        0,
                        false),
                Arguments.of(
                        "round7: bounded-wildcard-4-variable",
                        "import java.util.*; import java.util.function.*; class Example  {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} } <U extends CharSequence> void test(){ Supplier<Mono<List<List<? extends U>>>> xs=()->null; Mono.defer(xs).consume(s -> s.get(0).get(0).length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.util.List<java.util.List<? extends U>>>|Example.Mono",
                            "length|int|java.lang.CharSequence",
                            "get|? extends U|java.util.List",
                            "get|java.util.List<? extends U>|java.util.List"
                        },
                        0,
                        false),
                Arguments.of(
                        "round8: final-bound-chain-0-expression",
                        "import java.util.*; import java.util.function.*; class Example {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> f){return null;} } <U extends CharSequence> void test(){Mono.defer(() -> (Mono<List<? extends U>>)null).map(s -> (U)s.get(0)).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "map|Example.Mono<U>|Example.Mono",
                            "defer|Example.Mono<java.util.List<? extends U>>|Example.Mono",
                            "get|? extends U|java.util.List",
                            "length|int|java.lang.CharSequence"
                        },
                        0,
                        false),
                Arguments.of(
                        "round8: final-bound-chain-0-block",
                        "import java.util.*; import java.util.function.*; class Example {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> f){return null;} } <U extends CharSequence> void test(){Mono.defer(() -> {return (Mono<List<? extends U>>)null;}).map(s -> (U)s.get(0)).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "map|Example.Mono<U>|Example.Mono",
                            "defer|Example.Mono<java.util.List<? extends U>>|Example.Mono",
                            "get|? extends U|java.util.List",
                            "length|int|java.lang.CharSequence"
                        },
                        0,
                        false),
                Arguments.of(
                        "round8: final-bound-chain-1-expression",
                        "import java.util.*; import java.util.function.*; class Example {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> f){return null;} } <U extends CharSequence> void test(){Mono.defer(() -> (Mono<Map<String, ? extends U>>)null).map(s -> s.get(\"x\").length()).consume(s -> s.intValue());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "map|Example.Mono<java.lang.Integer>|Example.Mono",
                            "defer|Example.Mono<java.util.Map<java.lang.String,? extends U>>|Example.Mono",
                            "length|int|java.lang.CharSequence",
                            "get|? extends U|java.util.Map",
                            "intValue|int|java.lang.Integer"
                        },
                        0,
                        false),
                Arguments.of(
                        "round8: final-bound-chain-1-block",
                        "import java.util.*; import java.util.function.*; class Example {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> f){return null;} } <U extends CharSequence> void test(){Mono.defer(() -> {return (Mono<Map<String, ? extends U>>)null;}).map(s -> s.get(\"x\").length()).consume(s -> s.intValue());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "map|Example.Mono<java.lang.Integer>|Example.Mono",
                            "defer|Example.Mono<java.util.Map<java.lang.String,? extends U>>|Example.Mono",
                            "length|int|java.lang.CharSequence",
                            "get|? extends U|java.util.Map",
                            "intValue|int|java.lang.Integer"
                        },
                        0,
                        false),
                Arguments.of(
                        "round8: final-bound-chain-2-expression",
                        "import java.util.*; import java.util.function.*; class Example {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> f){return null;} } <U extends CharSequence> void test(){Mono.defer(() -> (Mono<List<? extends U>>)null).consume(s -> { U first=s.get(0); first.length(); });} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.util.List<? extends U>>|Example.Mono",
                            "get|? extends U|java.util.List",
                            "length|int|java.lang.CharSequence"
                        },
                        0,
                        false),
                Arguments.of(
                        "round8: final-bound-chain-2-block",
                        "import java.util.*; import java.util.function.*; class Example {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> f){return null;} } <U extends CharSequence> void test(){Mono.defer(() -> {return (Mono<List<? extends U>>)null;}).consume(s -> { U first=s.get(0); first.length(); });} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "defer|Example.Mono<java.util.List<? extends U>>|Example.Mono",
                            "get|? extends U|java.util.List",
                            "length|int|java.lang.CharSequence"
                        },
                        0,
                        false),
                Arguments.of(
                        "round8: final-bound-chain-3-expression",
                        "import java.util.*; import java.util.function.*; class Example {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> f){return null;} } <U extends CharSequence> void test(){Mono.defer(() -> (Mono<List<? extends U>>)null).map(s -> s.get(0).subSequence(0,1)).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "map|Example.Mono<java.lang.CharSequence>|Example.Mono",
                            "defer|Example.Mono<java.util.List<? extends U>>|Example.Mono",
                            "subSequence|java.lang.CharSequence|java.lang.CharSequence",
                            "get|? extends U|java.util.List",
                            "length|int|java.lang.CharSequence"
                        },
                        0,
                        false),
                Arguments.of(
                        "round8: final-bound-chain-3-block",
                        "import java.util.*; import java.util.function.*; class Example {static abstract class Mono<T>{ static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> xs){return null;} void consume(Consumer<? super T> action){} <R> Mono<R> map(Function<? super T,? extends R> f){return null;} } <U extends CharSequence> void test(){Mono.defer(() -> {return (Mono<List<? extends U>>)null;}).map(s -> s.get(0).subSequence(0,1)).consume(s -> s.length());} }",
                        new String[] {
                            "consume|void|Example.Mono",
                            "map|Example.Mono<java.lang.CharSequence>|Example.Mono",
                            "defer|Example.Mono<java.util.List<? extends U>>|Example.Mono",
                            "subSequence|java.lang.CharSequence|java.lang.CharSequence",
                            "get|? extends U|java.util.List",
                            "length|int|java.lang.CharSequence"
                        },
                        0,
                        false));
    }
}
