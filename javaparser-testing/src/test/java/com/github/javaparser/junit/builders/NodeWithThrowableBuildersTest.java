package com.github.javaparser.junit.builders;

import static org.junit.Assert.assertEquals;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.type.ClassOrInterfaceType;

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
		addMethod.addThrownType(IllegalStateException.class);
		assertEquals(1, addMethod.getThrownTypes().size());
		assertEquals(true, addMethod.isThrown(IllegalStateException.class));
		addMethod.addThrownType(new ClassOrInterfaceType("Test"));
		assertEquals(2, addMethod.getThrownTypes().size());
		assertEquals("Test", addMethod.getThrownType(1).toString());
	}
}