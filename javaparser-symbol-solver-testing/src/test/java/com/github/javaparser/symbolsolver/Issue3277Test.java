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

import java.io.IOException;
import java.nio.file.Path;

import org.junit.jupiter.api.Test;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

public class Issue3277Test extends AbstractResolutionTest {

	@Test
	void test() throws IOException {
		String code =
				"public class StackOverflowTestCase {\n"
				+ "	private C c = new C();\n"
				+ "\n"
				+ "	public void method1() {\n"
				+ "		String localVariable = ConstantA.b.new innerClassInB(c.d.str1, c.d.str2).toString();\n"
				+ "	}\n"
				+ "}";
		Path pathToSourceFile = adaptPath("src/test/resources/issue3277");
		ParserConfiguration parserConfiguration = new ParserConfiguration();
        JavaSymbolSolver symbolSolver = new JavaSymbolSolver(new CombinedTypeSolver(new ReflectionTypeSolver(), new JavaParserTypeSolver(pathToSourceFile)));
	    parserConfiguration.setSymbolResolver(symbolSolver);
	    JavaParser javaParser = new JavaParser(parserConfiguration);
	    CompilationUnit cu = javaParser.parse(code).getResult().get();
	    MethodCallExpr methodCallExpr = cu.findFirst(MethodCallExpr.class).orElse(null);
	    assertEquals("java.lang.Object.toString()", methodCallExpr.resolve().getQualifiedSignature());
	}
}
