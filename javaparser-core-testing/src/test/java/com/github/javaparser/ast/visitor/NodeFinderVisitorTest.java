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

package com.github.javaparser.ast.visitor;

import static com.github.javaparser.StaticJavaParser.parse;
import static org.junit.jupiter.api.Assertions.*;

import org.junit.jupiter.api.Test;

import com.github.javaparser.Position;
import com.github.javaparser.Range;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.type.Type;

class NodeFinderVisitorTest {
	
	NodeFinderVisitor finder = new NodeFinderVisitor(NodeFinderVisitor.fConveringNode);

	@Test
	void testNoCoveringNode() {
		CompilationUnit cu = parse("class X { }");
		Position position = new Position(0,0);
		Range range = new Range(position, position);
		cu.accept(finder, range);
		assertTrue(finder.getSelectedNode() == null);
	}
	
	@Test
	void testClassOrInterfaceDeclarationIsCovering() {
		CompilationUnit cu = parse("class X { }");
		ClassOrInterfaceDeclaration cid = cu.findFirst(ClassOrInterfaceDeclaration.class).get();
		Range range = new Range(Position.HOME, Position.HOME);
		cu.accept(finder, range);
		assertEquals(cid , finder.getSelectedNode());
	}
	
	@Test
	void testClassOrInterfaceDeclarationIsCovering2() {
		CompilationUnit cu = parse("class X { }");
		ClassOrInterfaceDeclaration cid = cu.findFirst(ClassOrInterfaceDeclaration.class).get();
		cu.accept(finder, range(1, 11));
		assertEquals(cid , finder.getSelectedNode());
	}
	
	@Test
	void testClassOrInterfaceDeclarationCovering() {
		CompilationUnit cu = parse(
				"class X {\n" +
				"  Boolean f;\n" +
				"}");
		
		ClassOrInterfaceDeclaration cid = cu.findFirst(ClassOrInterfaceDeclaration.class).get();
		cu.accept(finder, range(2, 11));
		assertEquals(cid , finder.getSelectedNode());
	}
	
	@Test
	void testNoCoveringOrCoveredNode2() {
		CompilationUnit cu = parse(
				"class X {\n" +
				"  void f() {\n" +
				"     int i = 0;\n" +
				"  }\n" +
				"}");
		MethodDeclaration md = cu.findFirst(MethodDeclaration.class).get();
		cu.accept(finder, range(3, 11));
		System.out.println(finder.getSelectedNode().toString());
		assertEquals(md.getBody().get() , finder.getSelectedNode());
	}
	
	private Range range(int line, int length) {
		return range(line, 1, length);
	}
	
	private Range range(int line, int begin, int length) {
		return new Range(new Position(line, begin), new Position(line, length));
	}
	
}
