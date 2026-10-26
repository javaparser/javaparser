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

import com.github.javaparser.JavaParserAdapter;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import java.util.List;
import org.junit.jupiter.api.Test;

public class Issue5196Test extends AbstractResolutionTest {

    @Test
    void testTypeVariableInferredFromSeveralArgumentsUsesLeastUpperBound() {
        String testCase = "class Example {\n"
                + "    static <T> T two(T a, T b) { return null; }\n"
                + "    void test(Integer a, Double b) {\n"
                + "        Example.two(a, b);\n"
                + "        Example.two(b, a);\n"
                + "    }\n"
                + "}\n";

        CompilationUnit cu = JavaParserAdapter.of(createParserWithResolver(defaultTypeSolver()))
                .parse(testCase);

        List<MethodCallExpr> calls = cu.findAll(MethodCallExpr.class);
        ResolvedType type1 = calls.get(0).calculateResolvedType();
        ResolvedType type2 = calls.get(1).calculateResolvedType();

        assertEquals("java.lang.Number", type1.describe());
        assertEquals("java.lang.Number", type2.describe());
    }

    @Test
    void testThreeArgumentsTypeVariableInferredUsesLeastUpperBound() {
        String testCase = "class Example {\n"
                + "    static <T> T three(T a, T b, T c) { return null; }\n"
                + "    void test(Integer a, Double b, Long c) {\n"
                + "        Example.three(a, b, c);\n"
                + "        Example.three(c, b, a);\n"
                + "    }\n"
                + "}\n";

        CompilationUnit cu = JavaParserAdapter.of(createParserWithResolver(defaultTypeSolver()))
                .parse(testCase);

        List<MethodCallExpr> calls = cu.findAll(MethodCallExpr.class);
        ResolvedType type1 = calls.get(0).calculateResolvedType();
        ResolvedType type2 = calls.get(1).calculateResolvedType();

        assertEquals("java.lang.Number", type1.describe());
        assertEquals("java.lang.Number", type2.describe());
    }

    @Test
    void testHierarchicalTypesVariableInferredUsesLeastUpperBound() {
        String testCase = "interface Base {}\n"
                + "class SubA implements Base {}\n"
                + "class SubB implements Base {}\n"
                + "class Example {\n"
                + "    static <T> T choose(T a, T b) { return null; }\n"
                + "    void test(SubA a, SubB b) {\n"
                + "        Example.choose(a, b);\n"
                + "        Example.choose(b, a);\n"
                + "    }\n"
                + "}\n";

        CompilationUnit cu = JavaParserAdapter.of(createParserWithResolver(defaultTypeSolver()))
                .parse(testCase);

        List<MethodCallExpr> calls = cu.findAll(MethodCallExpr.class);
        ResolvedType type1 = calls.get(0).calculateResolvedType();
        ResolvedType type2 = calls.get(1).calculateResolvedType();

        assertEquals("Base", type1.describe());
        assertEquals("Base", type2.describe());
    }
}
