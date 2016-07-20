package com.github.javaparser.junit.builders;

import org.junit.After;
import org.junit.Before;

import com.github.javaparser.ast.CompilationUnit;

public class NodeWithModifiersBuildersTest {
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
	NodeWithModifiers:
	default T addModifier(Modifier modifier) {
	default boolean isStatic() {
	default boolean isAbstract() {
	default boolean isFinal() {
	default boolean isNative() {
	default boolean isPrivate() {
	default boolean isProtected() {
	default boolean isPublic() {
	default boolean isStrictfp() {
	default boolean isSynchronized() {
	default boolean isTransient() {
	default boolean isVolatile() {
	*/
}