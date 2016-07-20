package com.github.javaparser.junit.builders;

import org.junit.After;
import org.junit.Before;

import com.github.javaparser.ast.CompilationUnit;

public class NodeWithMembersBuildersTest {
	CompilationUnit cu;

	@Before
	public void setup() {
		cu = new CompilationUnit();
	}

	@After
	public void teardown() {
		cu = null;
	}
	/*
	NodeWithMembers:
	
	public default FieldDeclaration addField(Class<?> typeClass, EnumSet<Modifier> modifiers, String name) {
	public default FieldDeclaration addField(String type, EnumSet<Modifier> modifiers, String name) {
	public default MethodDeclaration addMethod(String methodName, EnumSet<Modifier> modifiers) {
	public default ConstructorDeclaration addCtor(EnumSet<Modifier> modifiers) {
	public default BlockStmt addInitializer() {
	public default BlockStmt addStaticInitializer() {
	public default List<MethodDeclaration> getMethodsWithName(String name) {
	public default List<MethodDeclaration> getMethodsWithParameterTypes(String... paramTypes) {
	public default FieldDeclaration getFieldWithName(String name) {
	*/
}
