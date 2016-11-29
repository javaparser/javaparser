package com.github.javaparser.junit.ast.type;

import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.expr.ArrayCreationExpr;
import com.github.javaparser.ast.expr.MarkerAnnotationExpr;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.type.ArrayType;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.ast.type.Type;
import org.assertj.core.api.Assertions;
import org.junit.Test;

import static com.github.javaparser.JavaParser.*;
import static com.github.javaparser.ast.type.ArrayType.arrayOf;
import static com.github.javaparser.utils.Utils.EOL;
import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.Assert.assertEquals;

public class TypeConstructionTest {
    @Test
    public void getFieldDeclarationWithArrays() {
        FieldDeclaration fieldDeclaration = (FieldDeclaration) parseClassBodyDeclaration("@C int @A[] @B[] a @X[] @Y[];");

        ArrayType arrayType1 = (ArrayType) fieldDeclaration.getVariable(0).getType();
        ArrayType arrayType2 = (ArrayType) arrayType1.getComponentType();
        ArrayType arrayType3 = (ArrayType) arrayType2.getComponentType();
        ArrayType arrayType4 = (ArrayType) arrayType3.getComponentType();
        PrimitiveType elementType = (PrimitiveType) arrayType4.getComponentType();

        assertThat(arrayType1.getAnnotations()).containsExactly(new MarkerAnnotationExpr(Name.parse("A")));
        assertThat(arrayType2.getAnnotations()).containsExactly(new MarkerAnnotationExpr(Name.parse("B")));
        assertThat(arrayType3.getAnnotations()).containsExactly(new MarkerAnnotationExpr(Name.parse("X")));
        assertThat(arrayType4.getAnnotations()).containsExactly(new MarkerAnnotationExpr(Name.parse("Y")));

        assertThat(elementType.getType()).isEqualTo(PrimitiveType.Primitive.INT);
        assertThat(fieldDeclaration.getAnnotations()).containsExactly(new MarkerAnnotationExpr(Name.parse("C")));

        assertThat(fieldDeclaration.getElementType().getParentNode().get()).isSameAs(fieldDeclaration);
    }

    @Test
    public void getVariableDeclarationWithArrays() {
        ExpressionStmt variableDeclarationStatement = (ExpressionStmt) parseStatement("@C int @A[] @B[] a @X[] @Y[];");
        VariableDeclarationExpr variableDeclarationExpr = (VariableDeclarationExpr) variableDeclarationStatement.getExpression();

        ArrayType arrayType1 = (ArrayType) variableDeclarationExpr.getVariable(0).getType();
        ArrayType arrayType2 = (ArrayType) arrayType1.getComponentType();
        ArrayType arrayType3 = (ArrayType) arrayType2.getComponentType();
        ArrayType arrayType4 = (ArrayType) arrayType3.getComponentType();
        PrimitiveType elementType = (PrimitiveType) arrayType4.getComponentType();

        assertThat(arrayType1.getAnnotations()).containsExactly(new MarkerAnnotationExpr(Name.parse("A")));
        assertThat(arrayType2.getAnnotations()).containsExactly(new MarkerAnnotationExpr(Name.parse("B")));
        assertThat(arrayType3.getAnnotations()).containsExactly(new MarkerAnnotationExpr(Name.parse("X")));
        assertThat(arrayType4.getAnnotations()).containsExactly(new MarkerAnnotationExpr(Name.parse("Y")));

        assertThat(elementType.getType()).isEqualTo(PrimitiveType.Primitive.INT);
        assertThat(variableDeclarationExpr.getAnnotations()).containsExactly(new MarkerAnnotationExpr(Name.parse("C")));

        assertThat(variableDeclarationExpr.getElementType().getParentNode().get()).isSameAs(variableDeclarationExpr);
    }

    @Test
    public void getMethodDeclarationWithArrays() {
        MethodDeclaration methodDeclaration = (MethodDeclaration) parseClassBodyDeclaration("@C int @A[] a() @B[] {};");

        ArrayType arrayType1 = (ArrayType) methodDeclaration.getType();
        ArrayType arrayType2 = (ArrayType) arrayType1.getComponentType();
        Assertions.assertThat(arrayType2.getComponentType()).isInstanceOf(PrimitiveType.class);

        assertThat(arrayType1.getAnnotations()).containsExactly(new MarkerAnnotationExpr(Name.parse("A")));
        assertThat(arrayType2.getAnnotations()).containsExactly(new MarkerAnnotationExpr(Name.parse("B")));
        assertThat(methodDeclaration.getAnnotations()).containsExactly(new MarkerAnnotationExpr(Name.parse("C")));

        assertThat(methodDeclaration.getElementType().getParentNode().get()).isSameAs(methodDeclaration);
    }

    @Test
    public void getParameterWithArrays() {
        MethodDeclaration methodDeclaration = (MethodDeclaration) parseClassBodyDeclaration("void a(@C int @A[] a @B[]) {};");

        Parameter parameter = methodDeclaration.getParameter(0);

        ArrayType outerArrayType = (ArrayType) parameter.getType();

        ArrayType innerArrayType = (ArrayType) outerArrayType.getComponentType();
        PrimitiveType elementType = (PrimitiveType) innerArrayType.getComponentType();

        assertThat(elementType).isInstanceOf(PrimitiveType.class);
        assertThat(outerArrayType.getAnnotations()).containsExactly(new MarkerAnnotationExpr(Name.parse("A")));
        assertThat(innerArrayType.getAnnotations()).containsExactly(new MarkerAnnotationExpr(Name.parse("B")));
        assertThat(parameter.getAnnotations()).containsExactly(new MarkerAnnotationExpr(Name.parse("C")));

        assertThat(parameter.getElementType().getParentNode().get()).isSameAs(parameter);
    }

    @Test
    public void setVariableDeclarationWithArrays() {
        ExpressionStmt variableDeclarationStatement = (ExpressionStmt) parseStatement("@C int @A[] @B[] a @X[] @Y[];");
        VariableDeclarationExpr variableDeclarationExpr = (VariableDeclarationExpr) variableDeclarationStatement.getExpression();

        variableDeclarationExpr.getVariable(0).setType(arrayOf(arrayOf(PrimitiveType.INT_TYPE)));
        assertEquals("@C int a[][];", variableDeclarationStatement.toString());
    }

    @Test
    public void setFieldDeclarationWithArrays() {
        FieldDeclaration fieldDeclaration = (FieldDeclaration) parseClassBodyDeclaration("int[][] a[][];");
        fieldDeclaration.getVariable(0).setType(arrayOf(arrayOf(new ClassOrInterfaceType("Blob"))));

        assertEquals("Blob a[][];", fieldDeclaration.toString());
    }

    @Test
    public void setMethodDeclarationWithArrays() {
        MethodDeclaration method = (MethodDeclaration) parseClassBodyDeclaration("int[][] a()[][] {}");
        method.setType(arrayOf(arrayOf(new ClassOrInterfaceType("Blob"))));

        assertEquals("Blob[][] a() {" + EOL + "}", method.toString());
    }

    @Test
    public void setParameterWithArrays() {
        MethodDeclaration method = (MethodDeclaration) parseClassBodyDeclaration("void a(int[][] a[][]) {};");
        method.getParameter(0).setType(arrayOf(arrayOf(new ClassOrInterfaceType("Blob"))));

        assertEquals("void a(Blob[][] a) {" + EOL + "}", method.toString());
    }

    @Test
    public void getArrayCreationType() {
        ArrayCreationExpr expr = parseExpression("new int[]");
        ArrayType outerType = (ArrayType) expr.getType();
        Type<?> innerType = outerType.getComponentType();
        assertThat(innerType).isEqualTo(expr.getElementType());
    }
}
