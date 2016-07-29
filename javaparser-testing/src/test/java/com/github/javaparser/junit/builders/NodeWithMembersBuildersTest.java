package com.github.javaparser.junit.builders;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.List;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.TypeArguments;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.InitializerDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.ReferenceType;
import com.github.javaparser.ast.type.Type;

public class NodeWithMembersBuildersTest {
	CompilationUnit cu;
	private ClassOrInterfaceDeclaration classDeclaration;

	@Before
	public void setup() {
		cu = new CompilationUnit();
		classDeclaration = cu.addClass("test");
	}

	@After
	public void teardown() {
		cu = null;
		classDeclaration = null;
	}

	@Test
	public void testAddField() {
		FieldDeclaration addField = classDeclaration.addField(int.class, "fieldName", Modifier.PRIVATE);
		assertEquals(1, classDeclaration.getMembers().size());
		assertEquals(addField, classDeclaration.getMembers().get(0));
		assertEquals("fieldName", addField.getVariables().get(0).getId().getName());
	}

	@Test
	public void testAddMethod() {
		MethodDeclaration addMethod = classDeclaration.addMethod("foo", Modifier.PUBLIC);
		assertEquals(1, classDeclaration.getMembers().size());
		assertEquals(addMethod, classDeclaration.getMembers().get(0));
		assertEquals("foo", addMethod.getName());
	}

	@Test
	public void testAddCtor() {
		ConstructorDeclaration addCtor = classDeclaration.addCtor(Modifier.PUBLIC);
		assertEquals(1, classDeclaration.getMembers().size());
		assertEquals(addCtor, classDeclaration.getMembers().get(0));
		assertEquals(classDeclaration.getName(), addCtor.getName());
	}

	@Test
	public void testAddInitializers() {
		classDeclaration.addInitializer();
		assertEquals(1, classDeclaration.getMembers().size());
		assertEquals(InitializerDeclaration.class, classDeclaration.getMembers().get(0).getClass());

		classDeclaration.addStaticInitializer();
		assertEquals(2, classDeclaration.getMembers().size());
		assertEquals(InitializerDeclaration.class, classDeclaration.getMembers().get(0).getClass());
	}

	@Test
	public void testGetMethodsWithName() {
		MethodDeclaration addMethod = classDeclaration.addMethod("foo", Modifier.PUBLIC);
		MethodDeclaration addMethod2 = classDeclaration.addMethod("foo", Modifier.PUBLIC).addParameter(int.class, "overload");
		List<MethodDeclaration> methodsByName = classDeclaration.getMethodsByName("foo");
		assertEquals(2, methodsByName.size());
		assertTrue(methodsByName.contains(addMethod));
		assertTrue(methodsByName.contains(addMethod2));
	}

	@Test
	public void testGetMethodsWithParameterTypes() {
		classDeclaration.addMethod("foo", Modifier.PUBLIC);
		MethodDeclaration addMethod2 = classDeclaration.addMethod("foo", Modifier.PUBLIC).addParameter(int.class, "overload");
		ClassOrInterfaceType type = new ClassOrInterfaceType("List");
		ArrayList<Type> typeArguments = new ArrayList<>();
		typeArguments.add(new ClassOrInterfaceType("String"));
		type.setTypeArguments(TypeArguments.withArguments(typeArguments));
		MethodDeclaration methodWithListParam = classDeclaration.addMethod("fooList", Modifier.PUBLIC).addParameter(new ReferenceType(type), "overload");
		MethodDeclaration addMethod3 = classDeclaration.addMethod("foo2", Modifier.PUBLIC).addParameter(int.class, "overload");

		List<MethodDeclaration> methodsByParam = classDeclaration.getMethodsByParameterTypes(int.class);
		assertEquals(2, methodsByParam.size());
		assertTrue(methodsByParam.contains(addMethod2));
		assertTrue(methodsByParam.contains(addMethod3));
		List<MethodDeclaration> methodsByParam2 = classDeclaration.getMethodsByParameterTypes("List<String>");
		assertEquals(1, methodsByParam2.size());
		assertTrue(methodsByParam2.contains(methodWithListParam));
	}

	@Test
	public void testGetFieldWithName() {
		FieldDeclaration addField = classDeclaration.addField(int.class, "fieldName", Modifier.PRIVATE);
		classDeclaration.addField(float.class, "secondField", Modifier.PRIVATE);
		FieldDeclaration fieldByName = classDeclaration.getFieldByName("fieldName");
		assertEquals(addField, fieldByName);
	}
}
