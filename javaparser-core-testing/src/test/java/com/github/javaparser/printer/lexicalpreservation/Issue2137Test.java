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

import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.type.VoidType;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.utils.TestUtils.assertEqualsStringIgnoringEol;

public class Issue2137Test extends AbstractLexicalPreservingTest {

	@Test
	void test2137() {
	    considerCode( 
	            "public class Foo {\n" +
	            "  void mymethod1() {}\n" +
	            "  void mymethod2() {}\n" +
	            "}");
	    String expected = 
	            "public class Foo {\n" +
	            "  void mymethod1() {}\n" +
	            "  void mymethod3() {\n"+
	            "  }\n" +
	            "  \n" +
	            "  void mymethod2() {}\n" +
	            "}";
	    ClassOrInterfaceDeclaration cid = cu.getClassByName("Foo").get();
	    MethodDeclaration methodDeclaration = new MethodDeclaration();
	    methodDeclaration.setName("mymethod3");
	    methodDeclaration.setType(new VoidType());
	    cid.getMembers().add(1, methodDeclaration);

	    assertEqualsStringIgnoringEol(expected, LexicalPreservingPrinter.print(cu));
	}


}
