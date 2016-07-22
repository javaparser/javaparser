package com.github.javaparser.junit.builders;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;

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

	}

	@Test
	public void testAddMethod() {

	}

	@Test
	public void testAddCtor() {

	}

	@Test
	public void testAddInitializers() {

	}

	@Test
	public void testGetMethodsWithName() {

	}

	@Test
	public void testGetMethodsWithParameterTypes() {

	}

	@Test
	public void testGetFieldWithName() {

	}
	/*
     * NodeWithMembers:
     * public default FieldDeclaration addField(Type type, EnumSet<Modifier> modifiers, String name) {
     * public default MethodDeclaration addMethod(String methodName, EnumSet<Modifier> modifiers) {
     * public default ConstructorDeclaration addCtor(EnumSet<Modifier> modifiers) {
     * public default BlockStmt addInitializer() {
     * public default BlockStmt addStaticInitializer() {
     * public default List<MethodDeclaration> getMethodsWithName(String name) {
     * public default List<MethodDeclaration> getMethodsWithParameterTypes(String... paramTypes) {
     * public default FieldDeclaration getFieldWithName(String name) {
     */
}
