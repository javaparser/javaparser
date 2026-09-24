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
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

/**
 * Reproducer for <a href="https://github.com/javaparser/javaparser/issues/4991">#4991</a>.
 *
 * <p>Arrays of primitive types are invariant (JLS 4.10.3): an {@code int[]} argument is only
 * applicable to an {@code int[]} parameter, never to {@code long[]}, {@code float[]} or
 * {@code double[]}.
 */
class Issue4991Test extends AbstractResolutionTest {

    private static final String CODE_TEMPLATE = ""
            + "class Test {\n"
            + "  void m(%1$s[] arr) {\n"
            + "    Arrays.copyOf(arr, 3);\n"
            + "  }\n"
            + "}\n"
            + "class Arrays {\n"
            + "  public static native <T> T[] copyOf(T[] original, int newLength);\n"
            + "  public static native byte[] copyOf(byte[] original, int newLength);\n"
            + "  public static native short[] copyOf(short[] original, int newLength);\n"
            + "  public static native char[] copyOf(char[] original, int newLength);\n"
            + "  public static native int[] copyOf(int[] original, int newLength);\n"
            + "  public static native long[] copyOf(long[] original, int newLength);\n"
            + "  public static native float[] copyOf(float[] original, int newLength);\n"
            + "  public static native double[] copyOf(double[] original, int newLength);\n"
            + "}\n";

    @ParameterizedTest
    @ValueSource(strings = {"byte", "short", "char", "int", "long", "float", "double"})
    void primitiveArrayArgumentResolvesToExactOverload(String primitive) {
        ParserConfiguration config =
                new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));
        CompilationUnit cu = new JavaParser(config)
                .parse(String.format(CODE_TEMPLATE, primitive))
                .getResult()
                .get();
        MethodCallExpr call = cu.findFirst(MethodCallExpr.class).get();

        assertEquals("Arrays.copyOf(" + primitive + "[], int)", call.resolve().getQualifiedSignature());
    }
}
