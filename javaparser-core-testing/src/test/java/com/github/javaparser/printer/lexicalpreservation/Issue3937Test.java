/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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

package com.github.javaparser.printer.lexicalpreservation;

import static com.github.javaparser.utils.TestUtils.assertEqualsStringIgnoringEol;

import org.junit.jupiter.api.Test;

import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.stmt.ExpressionStmt;

public class Issue3937Test extends AbstractLexicalPreservingTest {
	static final String given = "package custom.project;\n" + "\n"
			+ "import java.util.stream.Stream;\n"
			+ "\n"
			+ "class TestFileSystemCodeProvider {\n"
			+ "	void testInMemoryFileSystem() {\n"
			+ "\n"
			+ "		Stream.of(\"\").listFilesForContent(file -> {\n"
			+ "			System.out.println(s);\n"
			+ "		});\n"
			+ "	}\n"
			+ "}\n"
			+ "";

	@Test
	void test() {
		considerCode(given);

		LexicalPreservingPrinter.setup(cu);

		LambdaExpr lambdaExpr = cu.findFirst(LambdaExpr.class).get();
		lambdaExpr.setBody(new ExpressionStmt(new MethodCallExpr(new NameExpr("SomeClass"), "someMethod")));

		String actual = LexicalPreservingPrinter.print(cu);
		String expected = "package custom.project;\n"
				+ "\n"
				+ "import java.util.stream.Stream;\n"
				+ "\n"
				+ "class TestFileSystemCodeProvider {\n"
				+ "	void testInMemoryFileSystem() {\n"
				+ "\n"
				+ "		Stream.of(\"\").listFilesForContent(file -> SomeClass.someMethod());\n"
				+ "	}\n"
				+ "}\n"
				+ "";
		assertEqualsStringIgnoringEol(expected, actual);
	}
}
