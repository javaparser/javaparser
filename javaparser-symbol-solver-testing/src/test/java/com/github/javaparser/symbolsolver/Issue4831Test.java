/*
 * Copyright (C) 2013-2026 The JavaParser Team.
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
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

/**
 * A type argument S matched against a formal {@code ? extends B} means S <: B, so the type variables of B must be
 * inferred from S, e.g. {@code T = String} for a {@code Supplier<Mono<String>>} passed to
 * {@code Supplier<? extends Mono<? extends T>>}.
 */
class Issue4831Test extends AbstractSymbolResolutionTest {

    private static final String MONO = "import java.util.function.*;\n"
            + "class Example {\n"
            + "    static abstract class Mono<T> {\n"
            + "        static <T> Mono<T> defer(Supplier<? extends Mono<? extends T>> supplier) { return null; }\n"
            + "        static <T> Mono<T> just(T value) { return null; }\n"
            + "        void consume(Consumer<? super T> consumer) {}\n"
            + "    }\n";

    private static final String MAPS = "import java.util.*;\n"
            + "class Example {\n"
            + "    static class Sub<X> extends HashMap<String, X> {}\n"
            + "    static class Swap<A, B> extends HashMap<B, A> {}\n"
            + "    static <K, V> V valueOfAny(List<? extends Map<K, V>> maps) { return null; }\n"
            + "    static <K, V> V value(Map<K, V> map) { return null; }\n";

    private static MethodCallExpr call(String code, String name) {
        ParserConfiguration configuration = new ParserConfiguration()
                .setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_8)
                .setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));
        CompilationUnit cu =
                new JavaParser(configuration).parse(code).getResult().get();
        return cu.findFirst(MethodCallExpr.class, call -> call.getNameAsString().equals(name))
                .get();
    }

    @Test
    void lambdaChainedOnACallInferredFromALambda() {
        MethodCallExpr length = call(
                MONO + "    void test() {\n"
                        + "        Mono.defer(() -> (Mono<String>) null).consume(s -> s.length());\n"
                        + "    }\n"
                        + "}",
                "length");

        assertEquals("int", length.calculateResolvedType().describe());
        assertEquals("java.lang.String.length()", length.resolve().getQualifiedSignature());
    }

    @Test
    void typeInferredFromABlockLambda() {
        MethodCallExpr defer = call(
                MONO + "    void test() {\n"
                        + "        Mono.defer(() -> { return Mono.just(\"a\"); }).consume(s -> s.length());\n"
                        + "    }\n"
                        + "}",
                "defer");

        assertEquals(
                "Example.Mono<java.lang.String>", defer.calculateResolvedType().describe());
    }

    @Test
    void typeInferredFromASupplierVariable() {
        MethodCallExpr defer = call(
                MONO + "    void test(Supplier<Mono<String>> supplier) {\n"
                        + "        Mono.defer(supplier);\n"
                        + "    }\n"
                        + "}",
                "defer");

        assertEquals(
                "Example.Mono<java.lang.String>", defer.calculateResolvedType().describe());
    }

    @Test
    void arrayTypeInferredFromALambda() {
        MethodCallExpr defer = call(
                MONO + "    void test() {\n" + "        Mono.defer(() -> (Mono<String[]>) null);\n" + "    }\n" + "}",
                "defer");

        assertEquals(
                "Example.Mono<java.lang.String[]>",
                defer.calculateResolvedType().describe());
    }

    @Test
    void typeInferredFromASubtypeWithFewerTypeParameters() {
        MethodCallExpr value = call(
                MAPS + "    void test(List<Sub<Integer>> maps) { Example.valueOfAny(maps); }\n" + "}", "valueOfAny");

        assertEquals("java.lang.Integer", value.calculateResolvedType().describe());
    }

    @Test
    void typeInferredFromASubtypeWithReorderedTypeParameters() {
        MethodCallExpr value = call(
                MAPS + "    void test(List<Swap<Integer, String>> maps) { Example.valueOfAny(maps); }\n" + "}",
                "valueOfAny");

        assertEquals("java.lang.Integer", value.calculateResolvedType().describe());
    }

    @Test
    void invariantTypeInferredFromASubtypeWithFewerTypeParameters() {
        // type arguments used to be matched by position, which overflowed Sub<X>'s single type argument
        MethodCallExpr value = call(MAPS + "    void test(Sub<Integer> map) { Example.value(map); }\n" + "}", "value");

        assertEquals("java.lang.Integer", value.calculateResolvedType().describe());
    }
}
