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

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

/**
 * An array passed directly to a variable arity method is only applicable in the fixed arity form, where the array
 * type must be assignable to the variadic parameter type as a whole. Its elements must not be widened or boxed
 * component by component the way grouped scalar arguments are: {@code int[]} is not a {@code double[]}, so a call
 * {@code m(new int[] {1})} does not match {@code m(double... v)}.
 *
 * @see <a href="https://github.com/javaparser/javaparser/issues/5146">#5146</a>
 */
class Issue5146Test extends AbstractSymbolResolutionTest {

    private static MethodCallExpr firstCall(String code) {
        ParserConfiguration configuration =
                new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));
        CompilationUnit cu =
                new JavaParser(configuration).parse(code).getResult().get();
        return cu.findAll(MethodCallExpr.class).stream()
                .filter(call -> call.getNameAsString().equals("m"))
                .findFirst()
                .get();
    }

    @Test
    void incompatibleArrayDoesNotMatchVariadicParameterOverOtherOverload() {
        String code = "class X {\n"
                + "    void m(double... v) {}\n"
                + "    void m(Object o) {}\n"
                + "    void t() {\n"
                + "        m(new int[] {1});\n"
                + "    }\n"
                + "}";

        // javac resolves this to m(Object): an int[] is not a double[], so m(double...) is not applicable.
        assertEquals("X.m(java.lang.Object)", firstCall(code).resolve().getQualifiedSignature());
    }

    @Test
    void incompatibleArrayDoesNotMatchVariadicParameter() {
        String code = "class X {\n"
                + "    void m(double... v) {}\n"
                + "    void t() {\n"
                + "        m(new int[] {1});\n"
                + "    }\n"
                + "}";

        // With no other overload, the call is not applicable at all, just as javac reports a compilation error.
        MethodCallExpr call = firstCall(code);
        assertThrows(UnsolvedSymbolException.class, call::resolve);
    }
}
