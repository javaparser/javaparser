package com.github.javaparser.junit.builders;

import org.junit.After;
import org.junit.Before;

import com.github.javaparser.ast.CompilationUnit;

public class NodeWithParametersBuildersTest {
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
	NodeWithParameters:
	
	default T addParameter(Type type, String name) {
	default T addParameter(Class<?> paramClass, String name) {
	default Parameter addAndGetParameter(Type type, String name) {
	default Parameter addAndGetParameter(Class<?> paramClass, String name) {
	*/
}