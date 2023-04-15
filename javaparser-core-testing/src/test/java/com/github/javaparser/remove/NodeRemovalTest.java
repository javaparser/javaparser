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

package com.github.javaparser.remove;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.printer.lexicalpreservation.AbstractLexicalPreservingTest;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

class NodeRemovalTest extends  AbstractLexicalPreservingTest{
	
	private final CompilationUnit compilationUnit = new CompilationUnit();

	@Test
	void testRemoveClassFromCompilationUnit() {
		ClassOrInterfaceDeclaration testClass = compilationUnit.addClass("test");
		assertEquals(1, compilationUnit.getTypes().size());
		boolean remove = testClass.remove();
		assertTrue(remove);
		assertEquals(0, compilationUnit.getTypes().size());
	}

	@Test
	void testRemoveFieldFromClass() {
		ClassOrInterfaceDeclaration testClass = compilationUnit.addClass("test");

		FieldDeclaration addField = testClass.addField(String.class, "test");
		assertEquals(1, testClass.getMembers().size());
		boolean remove = addField.remove();
		assertTrue(remove);
		assertEquals(0, testClass.getMembers().size());
	}

	@Test
	void testRemoveStatementFromMethodBody() {
		ClassOrInterfaceDeclaration testClass = compilationUnit.addClass("testC");

		MethodDeclaration addMethod = testClass.addMethod("testM");
		BlockStmt methodBody = addMethod.createBody();
		Statement addStatement = methodBody.addAndGetStatement("test");
		assertEquals(1, methodBody.getStatements().size());
		boolean remove = addStatement.remove();
		assertTrue(remove);
		assertEquals(0, methodBody.getStatements().size());
	}

	@Test
	void testRemoveStatementFromMethodBodyWithLexicalPreservingPrinter() {
		considerStatement("{\r\n" + "    log.error(\"context\", e);\r\n" +
				"    log.error(\"context\", e);\r\n" +
				"    throw new ApplicationException(e);\r\n" + "}\r\n");
		BlockStmt bstmt = statement.asBlockStmt();
		List<Node> children = bstmt.getChildNodes();
		remove(children.get(0));
		assertTrue(children.size() == 2);
		remove(children.get(0));
		assertTrue(children.size() == 1);
		assertTrue(children.stream().allMatch(n -> n.getParentNode() != null));
	}

	// remove the node and parent's node until response is true
	boolean remove(Node node) {
		boolean result = node.remove();
		if (!result && node.getParentNode().isPresent())
			result = remove(node.getParentNode().get());
		return result;
	}
}
