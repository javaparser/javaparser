package com.github.javaparser.junit.builders;

import static org.junit.Assert.assertEquals;

import java.util.List;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.body.VariableDeclaratorId;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.ReturnStmt;

public class FieldDeclarationBuildersTest {
	CompilationUnit cu;
	private ClassOrInterfaceDeclaration testClass;
	private EnumDeclaration testEnum;

	@Before
	public void setup() {
		cu = new CompilationUnit();
		testClass = cu.addClass("testClass");
		testEnum = cu.addEnum("testEnum");
	}

	@After
	public void teardown() {
		cu = null;
		testClass = null;
		testEnum = null;
	}

	@Test(expected = IllegalStateException.class)
	public void testOrphanFieldGetter() {
		new FieldDeclaration().createGetter();
	}

	@Test(expected = IllegalStateException.class)
	public void testOrphanFieldSetter() {
		new FieldDeclaration().createSetter();
	}

	@Test
	public void testCreateGetterInAClass() {
		testClass.addPrivateField(int.class, "myField").createGetter();
		assertEquals(2, testClass.getMembersList().size());
		assertEquals(MethodDeclaration.class, testClass.getMembersList().get(1).getClass());
		List<MethodDeclaration> methodsWithName = testClass.getMethodsByNameList("getMyField");
		assertEquals(1, methodsWithName.size());
		MethodDeclaration getter = methodsWithName.get(0);
		assertEquals("getMyField", getter.getName());
		assertEquals("int", getter.getType().toString());
		assertEquals(ReturnStmt.class, getter.getBody().getStmtsList().get(0).getClass());
	}

	@Test
	public void testCreateSetterInAClass() {
		testClass.addPrivateField(int.class, "myField").createSetter();
		assertEquals(2, testClass.getMembersList().size());
		assertEquals(MethodDeclaration.class, testClass.getMembersList().get(1).getClass());
		List<MethodDeclaration> methodsWithName = testClass.getMethodsByNameList("setMyField");
		assertEquals(1, methodsWithName.size());
		MethodDeclaration setter = methodsWithName.get(0);
		assertEquals("setMyField", setter.getName());
		assertEquals("int", setter.getParametersList().get(0).getType().toString());
		assertEquals(ExpressionStmt.class, setter.getBody().getStmtsList().get(0).getClass());
		assertEquals("this.myField = myField;", setter.getBody().getStmtsList().get(0).toString());
	}

	@Test
	public void testCreateGetterInEnum() {
		testEnum.addPrivateField(int.class, "myField").createGetter();
		assertEquals(2, testEnum.getMembersList().size());
		assertEquals(MethodDeclaration.class, testEnum.getMembersList().get(1).getClass());
		List<MethodDeclaration> methodsWithName = testEnum.getMethodsByNameList("getMyField");
		assertEquals(1, methodsWithName.size());
		MethodDeclaration getter = methodsWithName.get(0);
		assertEquals("getMyField", getter.getName());
		assertEquals("int", getter.getType().toString());
		assertEquals(ReturnStmt.class, getter.getBody().getStmtsList().get(0).getClass());
	}

	@Test
	public void testCreateSetterInEnum() {
		testEnum.addPrivateField(int.class, "myField").createSetter();
		assertEquals(2, testEnum.getMembersList().size());
		assertEquals(MethodDeclaration.class, testEnum.getMembersList().get(1).getClass());
		List<MethodDeclaration> methodsWithName = testEnum.getMethodsByNameList("setMyField");
		assertEquals(1, methodsWithName.size());
		MethodDeclaration setter = methodsWithName.get(0);
		assertEquals("setMyField", setter.getName());
		assertEquals("int", setter.getParametersList().get(0).getType().toString());
		assertEquals(ExpressionStmt.class, setter.getBody().getStmtsList().get(0).getClass());
		assertEquals("this.myField = myField;", setter.getBody().getStmtsList().get(0).toString());
	}

	@Test(expected = IllegalStateException.class)
	public void testCreateGetterWithANonValidField() {
		FieldDeclaration myPrivateField = testClass.addPrivateField(int.class, "myField");
		myPrivateField.getVariablesList().add(new VariableDeclarator(new VariableDeclaratorId("secondField")));
		myPrivateField.createGetter();
	}

	@Test(expected = IllegalStateException.class)
	public void testCreateSetterWithANonValidField() {
		FieldDeclaration myPrivateField = testClass.addPrivateField(int.class, "myField");
		myPrivateField.getVariablesList().add(new VariableDeclarator(new VariableDeclaratorId("secondField")));
		myPrivateField.createSetter();
	}

}
