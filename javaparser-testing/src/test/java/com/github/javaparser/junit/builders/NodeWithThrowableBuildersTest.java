package com.github.javaparser.junit.builders;

import static org.junit.Assert.assertEquals;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.ReferenceType;

public class NodeWithThrowableBuildersTest {
	CompilationUnit cu;

	@Before
	public void setup() {
		cu = new CompilationUnit();
	}

	@After
	public void teardown() {
		cu = null;
	}

	@Test
	public void testThrows() {
		MethodDeclaration addMethod = cu.addClass("test").addMethod("foo", Modifier.PUBLIC);
		addMethod.addThrows(IllegalStateException.class);
		assertEquals(1, addMethod.getThrowsList().size());
		assertEquals(true, addMethod.isThrows(IllegalStateException.class));
		addMethod.addThrows(new ReferenceType(new ClassOrInterfaceType("Test")));
		assertEquals(2, addMethod.getThrowsList().size());
		assertEquals("Test", addMethod.getThrowsList().get(1).getType().toString());
	}
}
