/*
 * Copyright (C) 2010 Júlio Vilmar Gesser.
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
 * Created on 17/01/2010
 */
package japa.parser.ast;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;

import fixture.Helper;
import japa.parser.ast.expr.NameExpr;

import org.junit.Test;

/**
 * @author Julio Vilmar Gesser
 */
public class TestHashCodeEquals {

	private void assertEqualsAndHashCode(final Object o1, final Object o2) {
		assertEquals(o1, o2);
		assertEquals(o1.hashCode(), o2.hashCode());
	}

	private void assertNotEqualsAndHashCode(final Object o1, final Object o2) {
		assertFalse("Not different equals", o1.equals(o2));
		assertFalse("Not different hashCode", o1.hashCode() == o2.hashCode());
	}

	private void assertNotEquals(final Object o1, final Object o2) {
		assertFalse("Not different equals", o1.equals(o2));
	}

	@Test public void tesCompilationUnitEqual() throws Exception {
		final String source = Helper.readStream(getClass().getResourceAsStream("DumperTestClass.java"));
		final CompilationUnit cu1 = Helper.parserString(source);
		final CompilationUnit cu2 = Helper.parserString(source);
		assertEqualsAndHashCode(cu1, cu2);
	}

	@Test public void tesCompilationUnitNotEqual() throws Exception {
		final String source = Helper.readStream(getClass().getResourceAsStream("DumperTestClass.java"));
		final CompilationUnit cu1 = Helper.parserString(source);
		final CompilationUnit cu2 = Helper.parserString(source);

		cu2.setPackage(new PackageDeclaration(new NameExpr("diff_package")));
		assertNotEqualsAndHashCode(cu1, cu2);
	}

	@Test public void testDiffClasses() throws Exception {
		final String source_with_comment = //
		"package japa.parser.javacc; " + //
				"public class Teste {}";
		final String source_without_comment = //
		"package japa.parser.javacc; " + //
				"public enum Teste {}";

		final CompilationUnit cu1 = Helper.parserString(source_with_comment);
		final CompilationUnit cu2 = Helper.parserString(source_without_comment);

		assertNotEqualsAndHashCode(cu1, cu2);
	}

	@Test public void testJavadoc() throws Exception {
		final String source = Helper.readStream(getClass().getResourceAsStream("JavadocTestClass.java"));
		final CompilationUnit cu1 = Helper.parserString(source);
		final CompilationUnit cu2 = Helper.parserString(source);
		assertEqualsAndHashCode(cu1, cu2);
	}

	private final String source_with_comment = //
	"package japa.parser.javacc;\n" + //
			"public class Teste {\n" + //
			"//line comment\n" + //
			"int a = 0;" + //
			"//line comment\r\n" + //
			"int b = 0;" + //
			"//line comment\r" + //
			"int c = 0;" + //
			"/* multi-line\n comment\n*/" + //
			"int d = 0;" + //
			"/** multi-line\r\n javadoc\n*/" + //
			"int e = 0;" + //
			"}\n" + //
			"//final comment" + //
			"";

	private final String source_without_comment = //
	"package japa.parser.javacc;\n" + //
			"\n" + //
			"public class Teste {\n" + //
			"\n" + //
			"    int a = 0;\n" + //
			"\n" + //
			"    int b = 0;\n" + //
			"\n" + //
			"    int c = 0;\n" + //
			"\n" + //
			"    int d = 0;\n" + //
			"\n" + //
			"    /** multi-line\r\n javadocwfwf\n*/\n" + //
			"    int e = 0;\n" + //
			"}\n" + //
			"";

    /**
     * Sample that also comments are considered when checking for equality.
     */
	@Test public void testCommentsDiff() throws Exception {

		final CompilationUnit cu1 = Helper.parserString(source_with_comment);
		final CompilationUnit cu2 = Helper.parserString(source_without_comment);

		// hashcode can be the same, equals() shall return false
		assertNotEquals(cu1, cu2);
	}

	@Test public void testCommentsEquals() throws Exception {

		final CompilationUnit cu1 = Helper.parserString(source_with_comment);
		final CompilationUnit cu2 = Helper.parserString(source_with_comment);

		assertEqualsAndHashCode(cu1, cu2);
	}
}