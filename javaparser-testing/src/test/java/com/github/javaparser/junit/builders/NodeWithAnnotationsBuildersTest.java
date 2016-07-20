package com.github.javaparser.junit.builders;

import org.junit.After;
import org.junit.Before;

import com.github.javaparser.ast.CompilationUnit;

public class NodeWithAnnotationsBuildersTest {
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
	NodeWithAnnotations
	
	public default NormalAnnotationExpr addAnnotation(String name) {
	public default NormalAnnotationExpr addAnnotation(Class<? extends Annotation> clazz) {
	public default T addMarkerAnnotation(String name) {
	public default T addMarkerAnnotation(Class<? extends Annotation> clazz) {
	public default T addSingleMemberAnnotation(String name, String value) {
	public default T addSingleMemberAnnotation(Class<? extends Annotation> clazz,
	public default boolean isAnnotationPresent(String annotationName) {
	public default boolean isAnnotationPresent(Class<? extends Annotation> annotationClass) {
	public default AnnotationExpr getAnnotationByName(String annotationName) {
	public default AnnotationExpr getAnnotationByName(Class<? extends Annotation> annotationClass) {
	*/

}