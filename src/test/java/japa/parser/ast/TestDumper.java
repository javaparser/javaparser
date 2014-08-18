/*
 * Copyright (C) 2007 Júlio Vilmar Gesser.
 * 
 * This file is part of Java 1.5 parser and Abstract Syntax Tree.
 *
 * Java 1.5 parser and Abstract Syntax Tree is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Java 1.5 parser and Abstract Syntax Tree is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with Java 1.5 parser and Abstract Syntax Tree.  If not, see <http://www.gnu.org/licenses/>.
 */
/*
 * Created on 22/11/2006
 */
package japa.parser.ast;

import static org.junit.Assert.assertEquals;

import fixture.Helper;
import japa.parser.ast.body.ClassOrInterfaceDeclaration;

import org.junit.Test;

/**
 * @author Julio Vilmar Gesser
 */
public class TestDumper {

	@Test public void testDumpVisitor() throws Exception {
		final String source = Helper.readStream(getClass().getResourceAsStream("DumperTestClass.java"));
		final CompilationUnit cu = Helper.parserString(source);
		assertEquals(source, cu.toString());
	}

	@Test public void testJavadoc() throws Exception {
		final String source = Helper.readStream(getClass().getResourceAsStream("JavadocTestClass.java"));
		final CompilationUnit cu = Helper.parserString(source);
		assertEquals(source, cu.toString());
		assertEquals(19, cu.getComments().size());
	}

	@Test public void testWithInlineCommentsNearFields() throws Exception {
		final String source_with_comment = //
		"package japa.parser.javacc;\n" + //
				"public class Teste {\n" + //
				"//line comment1 \n" + //
				"int a = 0; //line comment2  \r\n" + //
				"int b = 0; //line comment3 \r" + //
				"int c = 0;" + //
				"/* multi-line\n comment\n*/" + //
				"int d = 0;" + //
				"/** multi-line\r\n javadoc\n*/" + //
				"int e = 0;" + //
				"}\n" + //
				"//final comment" + //
				"";
		final String source_dumped = //
		"package japa.parser.javacc;\n" + //
				"\n" + //
				"public class Teste {\n" + //
				"\n" + //
				"    //line comment1 \n" + //
                "    //line comment2  \n" + //
                "    int a = 0;\n" + //
				"\n" + //
				// not-FIX_ME: not sure what all these trailing spaces are.
                // They spaces are there because the dumper indent the code
                // FIXME we should indent also the line of comments successive to the first
				"    //line comment3 \n" + //
				"    int b = 0;\n" + //
				"\n" + //
				"    int c = 0;\n" + //
				"\n" + //
				"    /* multi-line\n comment\n*/\n" + //
				"    int d = 0;\n" + //
				"\n" + //
				"    /** multi-line\n javadoc\n*/\n" + //
				"    int e = 0;\n" + //
				"}\n" + //
                "//final comment" + //
				"";

		final CompilationUnit cu = Helper.parserString(source_with_comment);
        assertEquals(6, cu.getAllContainedComments().size());
		assertEquals(source_dumped.trim(), cu.toString().trim());
	}

    @Test public void testOrphanComments() throws Exception {
        final String originalSource = "class /*Comment1*/ A {\n" +
                "   //comment2\n" +
                "    // comment3\n" +
                "    int a;\n" +
                "    /**comment4\n" +
                "     * \n" +
                "     * */\n" +
                "//comment5    \n" +
                " }";

        final String dumpedSource =
                "class A {\n\n"+
                "    /*Comment1*/\n" +
                "    //comment2\n" +
                "    // comment3\n" +
                "    int a;\n" +
                "    /**comment4\n" +
                "     * \n" +
                "     * */\n" +
                "    //comment5    \n" +
                "}";

        final CompilationUnit cu = Helper.parserString(originalSource);
        ClassOrInterfaceDeclaration classDecl = (ClassOrInterfaceDeclaration)cu.getTypes().get(0);
        assertEquals(4,classDecl.getOrphanComments().size());
        assertEquals("Comment1",classDecl.getOrphanComments().get(0).getContent());
        assertEquals(dumpedSource.trim(), cu.toString().trim());
    }
}