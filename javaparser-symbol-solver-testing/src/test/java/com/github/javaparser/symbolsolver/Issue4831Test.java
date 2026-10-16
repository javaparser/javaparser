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
        CompilationUnit cu = new JavaParser(configuration).parse(code).getResult().orElseThrow(AssertionError::new);

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
