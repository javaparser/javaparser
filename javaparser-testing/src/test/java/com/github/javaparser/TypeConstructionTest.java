package com.github.javaparser;

import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.expr.MarkerAnnotationExpr;
import com.github.javaparser.ast.type.ArrayType;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.PrimitiveType;
import org.assertj.core.api.Assertions;
import org.junit.Test;

import static com.github.javaparser.JavaParser.parseClassBodyDeclaration;
import static com.github.javaparser.ast.expr.NameExpr.name;
import static com.github.javaparser.ast.type.ArrayType.arrayOf;
import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.Assert.assertEquals;

public class TypeConstructionTest {
    @Test
    public void getFieldDeclarationWithArrays() {
        FieldDeclaration fieldDeclaration = (FieldDeclaration) parseClassBodyDeclaration("@C int @A[] @B[] a @X[] @Y[];");

        ArrayType arrayType1 = (ArrayType) fieldDeclaration.getVariables().get(0).getType();
        ArrayType arrayType2 = (ArrayType) arrayType1.getComponentType();
        ArrayType arrayType3 = (ArrayType) arrayType2.getComponentType();
        ArrayType arrayType4 = (ArrayType) arrayType3.getComponentType();
        PrimitiveType elementType = (PrimitiveType) arrayType4.getComponentType();

        assertThat(arrayType1.getAnnotations()).containsExactly(new MarkerAnnotationExpr(name("A")));
        assertThat(arrayType2.getAnnotations()).containsExactly(new MarkerAnnotationExpr(name("B")));
        assertThat(arrayType3.getAnnotations()).containsExactly(new MarkerAnnotationExpr(name("X")));
        assertThat(arrayType4.getAnnotations()).containsExactly(new MarkerAnnotationExpr(name("Y")));

        assertThat(elementType.getType()).isEqualTo(PrimitiveType.Primitive.Int);
        assertThat(fieldDeclaration.getAnnotations()).containsExactly(new MarkerAnnotationExpr(name("C")));
    }

    @Test
    public void getMethodDeclarationWithArrays() {
        MethodDeclaration methodDeclaration = (MethodDeclaration) parseClassBodyDeclaration("@C int @A[] a() @B[] {};");

        ArrayType arrayType1 = (ArrayType) methodDeclaration.getType();
        ArrayType arrayType2 = (ArrayType) arrayType1.getComponentType();
        Assertions.assertThat(arrayType2.getComponentType()).isInstanceOf(PrimitiveType.class);

        assertThat(arrayType1.getAnnotations()).containsExactly(new MarkerAnnotationExpr(name("A")));
        assertThat(arrayType2.getAnnotations()).containsExactly(new MarkerAnnotationExpr(name("B")));
        assertThat(methodDeclaration.getAnnotations()).containsExactly(new MarkerAnnotationExpr(name("C")));
    }

    @Test
    public void getParameterWithArrays() {
        MethodDeclaration methodDeclaration = (MethodDeclaration) parseClassBodyDeclaration("void a(@C int @A[] a @B[]) {};");

        Parameter parameter = methodDeclaration.getParameters().get(0);

        ArrayType outerArrayType = (ArrayType) parameter.getType();

        ArrayType innerArrayType = (ArrayType) outerArrayType.getComponentType();
        PrimitiveType elementType = (PrimitiveType) innerArrayType.getComponentType();

        assertThat(elementType).isInstanceOf(PrimitiveType.class);
        assertThat(outerArrayType.getAnnotations()).containsExactly(new MarkerAnnotationExpr(name("A")));
        assertThat(innerArrayType.getAnnotations()).containsExactly(new MarkerAnnotationExpr(name("B")));
        assertThat(parameter.getAnnotations()).containsExactly(new MarkerAnnotationExpr(name("C")));
    }

    @Test
    public void setFieldDeclarationWithArrays() {
        FieldDeclaration fieldDeclaration = (FieldDeclaration) parseClassBodyDeclaration("int[][] a[][];");
        fieldDeclaration.getVariables().get(0).setType(arrayOf(arrayOf(new ClassOrInterfaceType("Blob"))));

        assertEquals("Blob a[][];", fieldDeclaration.toString());
    }

    @Test
    public void setMethodDeclarationWithArrays() {
        MethodDeclaration method = (MethodDeclaration) parseClassBodyDeclaration("int[][] a()[][] {}");
        method.setType(arrayOf(arrayOf(new ClassOrInterfaceType("Blob"))));

        assertEquals("Blob[][] a() {\n}", method.toString());
    }

    @Test
    public void setParameterWithArrays() {
        MethodDeclaration method = (MethodDeclaration) parseClassBodyDeclaration("void a(int[][] a[][]) {};");
        method.getParameters().get(0).setType(arrayOf(arrayOf(new ClassOrInterfaceType("Blob"))));

        assertEquals("void a(Blob[][] a) {\n}", method.toString());
    }
}
