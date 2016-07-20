package com.github.javaparser.junit.builders;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import com.github.javaparser.ast.CompilationUnit;

/*ClassOrInterfaceDeclaration:

public ClassOrInterfaceDeclaration addExtends(Class<?> clazz) {
public ClassOrInterfaceDeclaration addExtends(String name) {
public ClassOrInterfaceDeclaration addImplements(String name) {
public ClassOrInterfaceDeclaration addImplements(Class<?> clazz) {*/

public class ClassOrInterfaceDeclarationBuildersTest {
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
	public void testAddExtends() {

	}
}