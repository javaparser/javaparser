/*
 * Copyright (C) 2013-2023 The JavaParser Team.
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

import java.util.List;
import java.util.stream.Collectors;

import org.junit.jupiter.api.Test;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

public class Issue3866Test extends AbstractResolutionTest {

	@Test
	void test() {
		
		String code = 
				"public interface MyActivity {\n"
				+ "  class MyTimestamps {}\n"
				+ "    MyTimestamps getTimestamps();\n"
				+ "  }\n"
				+ "\n"
				+ "  public interface MyRichPresence extends MyActivity { }\n"
				+ "\n"
				+ "  class MyActivityImpl implements MyActivity {\n"
				+ "    @Override\n"
				+ "    public MyActivityImpl.MyTimestamps getTimestamps() {\n"
				+ "      return timestamps;\n"
				+ "  }\n"
				+ "}";
		
		final JavaSymbolSolver solver = new JavaSymbolSolver(new ReflectionTypeSolver(false));
		StaticJavaParser.getParserConfiguration().setSymbolResolver(solver);
        final CompilationUnit compilationUnit = StaticJavaParser.parse(code);

        final List<String> returnTypes = compilationUnit.findAll(MethodDeclaration.class)
                .stream()
                .map(md -> md.resolve())
                .map(rmd -> rmd.getReturnType().describe())
                .collect(Collectors.toList());

        returnTypes.forEach(type -> assertEquals("MyActivity.MyTimestamps", type));
	}
}
