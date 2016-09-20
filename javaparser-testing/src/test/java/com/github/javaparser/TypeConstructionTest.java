package com.github.javaparser;

import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.expr.MarkerAnnotationExpr;
import com.github.javaparser.ast.type.ArrayType;
import com.github.javaparser.ast.type.PrimitiveType;
import org.junit.Test;

import static com.github.javaparser.JavaParser.parseClassBodyDeclaration;
import static com.github.javaparser.ast.expr.NameExpr.name;
import static com.github.javaparser.ast.type.ArrayTypeAssert.assertThat;
import static com.github.javaparser.ast.type.PrimitiveTypeAssert.assertThat;
import static com.github.javaparser.ast.body.FieldDeclarationAssert.assertThat;

public class TypeConstructionTest {
	@Test
	public void testGetFieldDeclarationWithArrays() {
		FieldDeclaration fieldDeclaration = (FieldDeclaration) parseClassBodyDeclaration("@C int @A[] @B[] a @X[] @Y[];");

		ArrayType arrayType1 = (ArrayType) fieldDeclaration.getVariables().get(0).getId().getType();
		ArrayType arrayType2 = (ArrayType) arrayType1.getComponentType();
		ArrayType arrayType3 = (ArrayType) arrayType2.getComponentType();
		ArrayType arrayType4 = (ArrayType) arrayType3.getComponentType();
		PrimitiveType elementType = (PrimitiveType) arrayType4.getComponentType();

		assertThat(arrayType1).hasAnnotations(new MarkerAnnotationExpr(name("A")));
		assertThat(arrayType2).hasAnnotations(new MarkerAnnotationExpr(name("B")));
		assertThat(arrayType3).hasAnnotations(new MarkerAnnotationExpr(name("X")));
		assertThat(arrayType4).hasAnnotations(new MarkerAnnotationExpr(name("Y")));
		assertThat(elementType).hasType(PrimitiveType.Primitive.Int);
		assertThat(fieldDeclaration).hasAnnotations(new MarkerAnnotationExpr(name("C")));
	}

	@Test
	public void testGetMethodDeclarationWithArrays() {
		MethodDeclaration methodDeclaration = (MethodDeclaration) parseClassBodyDeclaration("int @A[] a() @B[] {};");

		ArrayType outerArrayType = (ArrayType) methodDeclaration.getType();

		ArrayType innerArrayType = (ArrayType) outerArrayType.getComponentType();
		PrimitiveType elementType = (PrimitiveType) innerArrayType.getComponentType();

		assertThat(elementType).hasType(PrimitiveType.Primitive.Int);
	}

	@Test
	public void testGetParameterWithArrays() {
		MethodDeclaration methodDeclaration = (MethodDeclaration) parseClassBodyDeclaration("void a(int @A[] a @B[]) {};");

		Parameter parameter = methodDeclaration.getParameters().get(0);

		ArrayType outerArrayType = (ArrayType) parameter.getType();

		ArrayType innerArrayType = (ArrayType) outerArrayType.getComponentType();
		PrimitiveType elementType = (PrimitiveType) innerArrayType.getComponentType();

		assertThat(elementType).hasType(PrimitiveType.Primitive.Int);
	}

	// TODO test setters
}
