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

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithStatements;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.RepeatedTest;
import org.junit.jupiter.api.Timeout;

import java.util.List;
import java.util.concurrent.TimeUnit;

/**
 * An issue when resolving some name when there are a series of many prior {@link NodeWithStatements}s.
 * Each queues up solving in the prior adjacent statement,
 * which means we queue up a factorial number of duplicate resolve calls.
 * <br>
 * This test verifies that parsing the given code below runs in an non-crazy amount of time <i>(Leeway for slow CI)</i>.
 * Without any fixes applied, this takes multiple hours to run.
 */
public class Issue3038Test extends AbstractResolutionTest {
	// The number of declarations to define
	private static final long MAX_ADJACENT_NODES = 500;
	// In no way should this take more than 2.5 seconds
	// Realistically this should take much less.
	private static final long TIME_LIMIT_MS = 2500;

	@RepeatedTest(10)
	@Timeout(value = TIME_LIMIT_MS, unit = TimeUnit.MILLISECONDS)
	public void test3038() {
		run(generate("        new Thread(){\n" +
				"            @Override\n" +
				"            public void run() {\n" +
				"                Foo foo = Foo.getInstance();\n" +
				"            }\n" +
				"        }.run();\n"));
	}

	@RepeatedTest(10)
	@Timeout(value = TIME_LIMIT_MS, unit = TimeUnit.MILLISECONDS)
	public void testAlt3038() {
		run(generate("        Foo foo = Foo.getInstance();\n"));
	}

	private void run(String code) {
		ParserConfiguration config = new ParserConfiguration();
		config.setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver(false)));
		StaticJavaParser.setConfiguration(config);

		CompilationUnit cu = StaticJavaParser.parse(code);

		List<NameExpr> exprs = cu.findAll(NameExpr.class);
		for (NameExpr expr : exprs) {
			long start = System.currentTimeMillis();
			try {
				expr.resolve();
			} catch (UnsolvedSymbolException ex) {
				// this is expected since we have no way for the resolver to find "Foo"
			}
			long end = System.currentTimeMillis();
			System.out.printf("Call to resolve '%s' took %dms", expr.toString(), (end - start));
		}
	}

	private String generate(String extra) {
		StringBuilder code = new StringBuilder(
				"public class Foo{\n" +
				"    public static void main(String[] args) {\n");
		for (int i = 0; i < MAX_ADJACENT_NODES; i++) {
			code.append(
				"        String s").append(i).append("   = \"hello\";\n");
		}
		code.append(
				extra  +
				"    }\n" +
				"    static Foo getInstance() {\n" +
				"        return new Foo();\n" +
				"    }\n" +
				"}");
		return code.toString();
	}
}
