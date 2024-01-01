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

import java.util.List;

import org.junit.jupiter.api.Test;

import com.github.javaparser.JavaParserAdapter;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodReferenceExpr;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;

public class Issue4037Test extends AbstractResolutionTest {

	@Test
	void test() {

		String code =
				"public class Test1 {\n"
						+ "	    public static Integer getD2() { return null; }\n"
						+ "	    public static Integer getD1() { return null; }\n"
						+ "	    public void m(java.util.function.Supplier... rs) { }\n"
						+ "\n"
						+ "	    public void test() {\n"
						+ "	        new Test1().m(Test1::getD1, Test1::getD2);    // exception throws\n"
						+ "	    }\n"
						+ "	}";

		JavaParserAdapter parser = JavaParserAdapter.of(createParserWithResolver(defaultTypeSolver()));
		CompilationUnit cu = parser.parse(code);

		List<MethodReferenceExpr > exprs = cu.findAll(MethodReferenceExpr .class);

		exprs.forEach(expr -> {
			assertDoesNotThrow(() -> expr.resolve());
		});
	}
}
