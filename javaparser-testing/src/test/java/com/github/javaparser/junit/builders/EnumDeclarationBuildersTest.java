package com.github.javaparser.junit.builders;

import org.junit.After;
import org.junit.Before;

import com.github.javaparser.ast.CompilationUnit;

public class EnumDeclarationBuildersTest {
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
	EnumDeclaration:
	
	public EnumDeclaration addImplements(String name) {
	public EnumDeclaration addImplements(Class<?> clazz) {
	public EnumConstantDeclaration addEnumConstant(String name) {
	
	*/
}