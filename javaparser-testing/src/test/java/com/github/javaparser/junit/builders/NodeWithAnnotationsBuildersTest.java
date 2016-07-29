package com.github.javaparser.junit.builders;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.expr.NormalAnnotationExpr;
import com.github.javaparser.ast.expr.SingleMemberAnnotationExpr;

public class NodeWithAnnotationsBuildersTest {
	CompilationUnit cu;
	private ClassOrInterfaceDeclaration testClass;

	@Before
	public void setup() {
		cu = new CompilationUnit();
		testClass = cu.addClass("testClass");
	}

	@interface hey {

	}

	@After
	public void teardown() {
		cu = null;
		testClass = null;
	}

	@Test
	public void testAddAnnotation() {
		NormalAnnotationExpr annotation = testClass.addAnnotation(hey.class);
		assertEquals("com.github.javaparser.junit.builders.NodeWithAnnotationsBuildersTest$hey", cu.getImports().get(0).getName().toString());
		assertEquals(1, testClass.getAnnotations().size());
		assertEquals(annotation, testClass.getAnnotations().get(0));
		assertEquals(NormalAnnotationExpr.class, testClass.getAnnotations().get(0).getClass());
	}

	@Test
	public void testAddMarkerAnnotation() {
		testClass.addMarkerAnnotation("test");
		assertEquals(1, testClass.getAnnotations().size());
	}

	@Test
	public void testAddSingleMemberAnnotation() {
		testClass.addSingleMemberAnnotation("test", "value");
		assertEquals(1, testClass.getAnnotations().size());
		assertEquals("value", ((SingleMemberAnnotationExpr) testClass.getAnnotations().get(0)).getMemberValue().toString());
	}

	@Test
	public void testIsAnnotationPresent() {
		testClass.addMarkerAnnotation(hey.class);
		assertTrue(testClass.isAnnotationPresent(hey.class));
	}

	@Test
	public void testGetAnnotationByName() {
		NormalAnnotationExpr annotation = testClass.addAnnotation(hey.class);
		assertEquals(annotation, testClass.getAnnotationByName("hey"));
	}

	@Test
	public void testGetAnnotationByClass() {
		NormalAnnotationExpr annotation = testClass.addAnnotation(hey.class);
		assertEquals(annotation, testClass.getAnnotationByClass(hey.class));
	}
}