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
import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.resolution.typesolvers.TypeSolverBuilder;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import org.junit.jupiter.api.Test;

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
        ParserConfiguration configuration = new ParserConfiguration()
                .setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_8)
                .setSymbolResolver(new JavaSymbolSolver(
                        new TypeSolverBuilder().withCurrentClassloader().build()));
        CompilationUnit cu =
                new JavaParser(configuration).parse(code).getResult().orElseThrow(AssertionError::new);

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
        return new JavaParser(configuration).parse(code).getResult().orElseThrow(AssertionError::new);
    }

    private MethodCallExpr findCall(CompilationUnit cu, String methodName) {
        return cu.findFirst(MethodCallExpr.class, call -> call.getNameAsString().equals(methodName))
                .orElseThrow(AssertionError::new);
    }
}
