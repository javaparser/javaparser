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

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

/**
 * {@code InferenceContext} used to key its inference variables by the bare name of a type
 * parameter, so two type parameters that merely share a name were unified into a single inference
 * variable and accumulated contradictory bounds.
 *
 * <p>{@code Stream.reduce(U, BiFunction<U, ? super T, U>, BinaryOperator<U>)} is the case that
 * surfaced it: the {@code U} of {@code reduce} (bound to {@code Integer} by the identity argument)
 * and the {@code U} of {@code BiFunction<T, U, R>} (bound to {@code String} through
 * {@code ? super T}) collapsed into one variable, and resolution failed with
 * {@code IllegalStateException: Equivalent types are: [String, ..., Integer]}.
 *
 * <p>Nothing about {@code Stream} or {@code reduce} is special here — any generic method whose type
 * parameter shares a name with a type parameter of a functional interface in its own signature is
 * affected.
 */
public class Issue5089Test extends AbstractResolutionTest {

    @Test
    void inferenceVariablesOfDistinctDeclarationsAreNotUnifiedByName() {
        String code = "import java.util.stream.Stream;\n" + "\n"
                + "public class A {\n"
                + "    public void test(){\n"
                + "        Stream.of(\"a\",\"bb\").reduce(0, (acc, s) -> acc + s.length(), (x, y) -> x + y);\n"
                + "    }\n"
                + "}";

        ParserConfiguration config = new ParserConfiguration();
        config.setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver(false)));
        StaticJavaParser.setConfiguration(config);

        CompilationUnit cu = StaticJavaParser.parse(code);

        MethodCallExpr reduce = cu.findAll(MethodCallExpr.class).stream()
                .filter(expr -> expr.getNameAsString().contentEquals("reduce"))
                .findFirst()
                .get();
        assertEquals("java.lang.Integer", reduce.calculateResolvedType().describe());

        LambdaExpr accumulator = cu.findFirst(LambdaExpr.class).get();
        assertEquals(
                "java.util.function.BiFunction<java.lang.Integer, ? super java.lang.String, java.lang.Integer>",
                accumulator.calculateResolvedType().describe());
    }
}
