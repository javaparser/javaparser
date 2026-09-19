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
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import java.util.List;
import org.junit.jupiter.api.Test;

/**
 * Overloads that only differ in their primitive array parameter type were reported as ambiguous.
 *
 * <p>{@code isBoxingCompatibleWithTypeSolver} recursed into the component types of two array types
 * and then accepted them through {@code isAssignableBy}, so {@code float[]} (and {@code double[]})
 * were considered applicable for an {@code int[]} argument because {@code float} is assignable by
 * {@code int}. Widening does not apply to array types, so all three overloads looked applicable and
 * resolution failed with {@code MethodAmbiguityException}.
 */
class Issue5065Test extends AbstractResolutionTest {

    @Test
    void overloadsDifferingOnlyInPrimitiveArrayParameterAreNotAmbiguous() {
        String code = "class Arrays {\n"
                + "    static int[] copyOf(int[] original, int newLength) { return original; }\n"
                + "    static float[] copyOf(float[] original, int newLength) { return original; }\n"
                + "    static double[] copyOf(double[] original, int newLength) { return original; }\n"
                + "}\n"
                + "class A {\n"
                + "    void test() {\n"
                + "        int[] ints = {1};\n"
                + "        float[] floats = {1f};\n"
                + "        Arrays.copyOf(ints, 1);\n"
                + "        Arrays.copyOf(floats, 1);\n"
                + "    }\n"
                + "}\n";

        ParserConfiguration configuration =
                new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver(false)));
        CompilationUnit cu =
                new JavaParser(configuration).parse(code).getResult().get();

        List<MethodCallExpr> calls = cu.findAll(MethodCallExpr.class);

        assertEquals("Arrays.copyOf(int[], int)", calls.get(0).resolve().getQualifiedSignature());
        assertEquals("Arrays.copyOf(float[], int)", calls.get(1).resolve().getQualifiedSignature());
    }
}
