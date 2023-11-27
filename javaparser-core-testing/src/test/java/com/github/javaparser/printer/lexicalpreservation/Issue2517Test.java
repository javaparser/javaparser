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

import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.utils.TestUtils.assertEqualsStringIgnoringEol;

public class Issue2517Test extends AbstractLexicalPreservingTest {

	@Test
	public void test() {

		considerCode("public class A {\n" +
	            "    public A(String a , String b) {\n" +
	            "    }\n" +
	            "    public static A m() {\n" +
	            "      return new A(\"a\",\"b\");\n" +
	            "    }\n" +
	            "}");
		
		String expected =
				"public class A {\n" +
			    "    public A(String a , String b) {\n" +
			    "    }\n" +
			    "    public static A m() {\n" +
			    "      return new A(\"b\", \"a\");\n" +
			    "    }\n" +
			    "}";

	    ObjectCreationExpr cd = cu.findFirst(ObjectCreationExpr.class).get();
	    NodeList<Expression> args = cd.getArguments();
	    Expression a1 = args.get(0);
	    Expression a2 = args.get(1);
	    NodeList<Expression> newArgs = new NodeList<>(a2, a1);
	    cd.setArguments(newArgs);

	    assertEqualsStringIgnoringEol(expected, LexicalPreservingPrinter.print(cu));
	}
}
