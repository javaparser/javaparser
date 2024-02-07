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

package com.github.javaparser.symbolsolver.javaparsermodel.contexts;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.util.List;
import java.util.stream.Collectors;

import org.junit.jupiter.api.*;

import com.github.javaparser.JavaParserAdapter;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

class JavaParserTypeDeclarationAdapterTest extends AbstractResolutionTest {

	@BeforeAll
	static void setUpBeforeClass() throws Exception {
	}

	@AfterAll
	static void tearDownAfterClass() throws Exception {
	}

	@BeforeEach
	void setUp() throws Exception {
	}

	@AfterEach
	void tearDownAfterEach() throws Exception {
	}

	@Test
	void issue3214() {
		String code =
				"public interface Foo {\n"
				+ "	    interface Bar {}\n"
				+ "	}\n"
				+ "\n"
				+ "	public interface Bar {\n"
				+ "	    void show();\n"
				+ "	}\n"
				+ "\n"
				+ "	public class Test implements Foo.Bar {\n"
				+ "	    private Bar bar;\n"
				+ "	    private void m() {\n"
				+ "	        bar.show();\n"
				+ "	    }\n"
				+ "	}";

		JavaParserAdapter parser = JavaParserAdapter.of(createParserWithResolver(defaultTypeSolver()));
		CompilationUnit cu = parser.parse(code);

		MethodCallExpr mce = cu.findAll(MethodCallExpr.class).get(0);

		assertEquals("Bar.show()",mce.resolve().getQualifiedSignature());
	}

	@Test
    void issue3946() {

        String code =
                "interface Activity {\n"
                + "class Timestamps {}\n"
                + "  Timestamps getTimestamps();\n"
                + "}\n"
                + "interface RichPresence extends Activity {}\n"
                + "  class ActivityImpl implements Activity {\n"
                + "    RichPresence.Timestamps timestamps;\n"
                + "    @Override\n"
                + "	   public RichPresence.Timestamps getTimestamps() { return timestamps; }\n"
                + "    }\n"
                + "class RichPresenceImpl extends ActivityImpl implements RichPresence { }";

        final JavaSymbolSolver solver = new JavaSymbolSolver(new ReflectionTypeSolver(false));
        StaticJavaParser.getParserConfiguration().setSymbolResolver(solver);
        final CompilationUnit compilationUnit = StaticJavaParser.parse(code);

        final List<String> returnTypes = compilationUnit.findAll(MethodDeclaration.class)
                .stream()
                .map(md -> md.resolve())
                .map(rmd -> rmd.getReturnType().describe())
                .collect(Collectors.toList());

        returnTypes.forEach(type -> assertEquals("Activity.Timestamps", type));
    }

}
