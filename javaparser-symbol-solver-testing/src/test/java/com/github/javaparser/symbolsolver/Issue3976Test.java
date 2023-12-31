/*
 * Copyright (C) 2013-2024 The JavaParser Team.
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

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledForJreRange;
import org.junit.jupiter.api.condition.JRE;

import com.github.javaparser.JavaParserAdapter;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;

public class Issue3976Test extends AbstractResolutionTest {

    @Test
    @EnabledForJreRange(min = JRE.JAVA_9)
    void test() {
    	String testCase =
				"import java.util.Map;\n"
				+ "public class Foo {\n"
				+ "		public Object m() {\n"
				+ "			return Map.of(\"k0\", 0, \"k1\", 1D);\n"
				+ "		}\n"
				+ "}";

		CompilationUnit cu = JavaParserAdapter.of(createParserWithResolver(defaultTypeSolver())).parse(testCase);

		MethodCallExpr methodCallExpr = cu.findFirst(MethodCallExpr.class).get();

		ResolvedType rt = methodCallExpr.calculateResolvedType();
		assertEquals("java.util.Map<java.lang.String, java.lang.Number>", rt.describe());
    }
}
