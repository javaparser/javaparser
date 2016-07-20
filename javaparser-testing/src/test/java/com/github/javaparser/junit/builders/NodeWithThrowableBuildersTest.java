package com.github.javaparser.junit.builders;

import org.junit.After;
import org.junit.Before;

import com.github.javaparser.ast.CompilationUnit;

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
	/*
	NodeWithThrowable:
	
	default T addThrows(ReferenceType throwType) {
	default T addThrows(Class<? extends Throwable> clazz) {
	public default boolean isThrows(Class<? extends Throwable> clazz) {
	public default boolean isThrows(String throwableName) {
	*/
}