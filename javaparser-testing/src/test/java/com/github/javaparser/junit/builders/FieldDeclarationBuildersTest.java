package com.github.javaparser.junit.builders;

import org.junit.After;
import org.junit.Before;

import com.github.javaparser.ast.CompilationUnit;

public class FieldDeclarationBuildersTest {
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
	FieldDeclaration
	public MethodDeclaration createGetter() {
	public MethodDeclaration createSetter() {
	*/
}
