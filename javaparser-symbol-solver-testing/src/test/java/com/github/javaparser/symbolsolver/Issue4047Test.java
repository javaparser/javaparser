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

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;

import java.util.List;

import org.junit.jupiter.api.Test;

import com.github.javaparser.JavaParserAdapter;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.MethodReferenceExpr;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

public class Issue4047Test extends AbstractResolutionTest {

	@Test
	void test() {

		String code =
				"import static java.lang.String.valueOf;\n"
				+ "public class MyClass { \n"
				+ "  void f() { \n"
				+ "    Long Integer = null; \n"
				+ "    Integer.intValue(); \n"
				+ "    valueOf(Integer); \n"
				+ "  } \n"
				+ "} \n";

		JavaParserAdapter parser = JavaParserAdapter.of(createParserWithResolver(defaultTypeSolver()));
		CompilationUnit cu = parser.parse(code);

		List<MethodCallExpr> exprs = cu.findAll(MethodCallExpr .class);

		assertEquals("java.lang.Long.intValue()", exprs.get(0).resolve().getQualifiedSignature());
		assertEquals("java.lang.String.valueOf(java.lang.Object)", exprs.get(1).resolve().getQualifiedSignature());
	}
}
