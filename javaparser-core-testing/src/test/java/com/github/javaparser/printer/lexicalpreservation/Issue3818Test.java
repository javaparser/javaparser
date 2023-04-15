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

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.expr.SimpleName;

import org.junit.jupiter.api.Test;

import static com.github.javaparser.utils.TestUtils.assertEqualsStringIgnoringEol;

public class Issue3818Test extends AbstractLexicalPreservingTest {

    @Test
    void test() {
        String src = "public class Foo {\n"
        		+ "\n"
				+ "    public Long[][] m(int[] a){}\n"
				+ "}";
        
        String expected = "public class Foo {\n"
        		+ "\n"
				+ "    public Long[][] m(int[] b){}\n"
				+ "}";

		BodyDeclaration<?> cu = StaticJavaParser.parseBodyDeclaration(src);
		MethodDeclaration md = cu.findAll(MethodDeclaration.class).get(0);
		LexicalPreservingPrinter.setup(md);
		Parameter p = md.getParameter(0);
		Parameter paramExpr = new Parameter(p.getModifiers(), p.getAnnotations(), p.getType(),
				p.isVarArgs(), p.getVarArgsAnnotations(), new SimpleName("b"));
		md.replace(p, paramExpr);
		assertEqualsStringIgnoringEol(expected, LexicalPreservingPrinter.print(cu));
    }
}
