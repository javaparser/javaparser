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

import com.github.javaparser.JavaParserAdapter;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;

public class Issue4124Test extends AbstractResolutionTest {

	@Test
	void issue4124_withDifferentTypeParameterName() {

		String code =
				"import java.util.Collections;\n"
				+ "import java.util.List;\n"
				+ "public class Foo<E> {\n"
				+ "    public void test(List<E> ls){\n"
				+ "        Collections.synchronizedList(ls);\n"
				+ "    }\n"
				+ "}\n";

		CompilationUnit cu = JavaParserAdapter.of(createParserWithResolver(defaultTypeSolver())).parse(code);

		MethodCallExpr m = cu.findFirst(MethodCallExpr.class).get();
		ResolvedMethodDeclaration rmd = m.resolve();
		assertEquals("java.util.Collections.synchronizedList(java.util.List<T>)", rmd.getQualifiedSignature());
	}

	@Test
	void issue4124_withSameTypeParameterName() {
		String code =
				"import java.util.Collections;\n"
				+ "import java.util.List;\n"
				+ "public class Foo<T> {\n"
				+ "    public void test(List<T> ls){\n"
				+ "        Collections.synchronizedList(ls);\n"
				+ "    }\n"
				+ "}\n";

		CompilationUnit cu = JavaParserAdapter.of(createParserWithResolver(defaultTypeSolver())).parse(code);

		MethodCallExpr m = cu.findFirst(MethodCallExpr.class).get();
		ResolvedMethodDeclaration rmd = m.resolve();
		assertEquals("java.util.Collections.synchronizedList(java.util.List<T>)", rmd.getQualifiedSignature());
	}
}
