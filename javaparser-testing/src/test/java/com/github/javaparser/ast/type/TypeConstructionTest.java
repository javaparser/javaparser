/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2016 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */

package com.github.javaparser.ast.type;

import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.expr.ArrayCreationExpr;
import com.github.javaparser.ast.expr.MarkerAnnotationExpr;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import org.assertj.core.api.Assertions;
import org.junit.Test;

import static com.github.javaparser.JavaParser.*;
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

        assertThat(arrayType1.getAnnotations()).containsExactly(new MarkerAnnotationExpr(parseName("A")));
        assertThat(arrayType2.getAnnotations()).containsExactly(new MarkerAnnotationExpr(parseName("B")));
        assertThat(arrayType3.getAnnotations()).containsExactly(new MarkerAnnotationExpr(parseName("X")));
        assertThat(arrayType4.getAnnotations()).containsExactly(new MarkerAnnotationExpr(parseName("Y")));

        assertThat(elementType.getType()).isEqualTo(PrimitiveType.Primitive.INT);
        assertThat(fieldDeclaration.getAnnotations()).containsExactly(new MarkerAnnotationExpr(parseName("C")));

        assertThat(arrayType1.getParentNode().get().getParentNode().get()).isSameAs(fieldDeclaration);
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

        assertThat(arrayType1.getAnnotations()).containsExactly(new MarkerAnnotationExpr(parseName("A")));
        assertThat(arrayType2.getAnnotations()).containsExactly(new MarkerAnnotationExpr(parseName("B")));
        assertThat(arrayType3.getAnnotations()).containsExactly(new MarkerAnnotationExpr(parseName("X")));
        assertThat(arrayType4.getAnnotations()).containsExactly(new MarkerAnnotationExpr(parseName("Y")));

        assertThat(elementType.getType()).isEqualTo(PrimitiveType.Primitive.INT);
        assertThat(variableDeclarationExpr.getAnnotations()).containsExactly(new MarkerAnnotationExpr(parseName("C")));

        assertThat(arrayType1.getParentNode().get().getParentNode().get()).isSameAs(variableDeclarationExpr);
    }

    @Test
    public void getMethodDeclarationWithArrays() {
        MethodDeclaration methodDeclaration = (MethodDeclaration) parseClassBodyDeclaration("@C int @A[] a() @B[] {};");

        ArrayType arrayType1 = (ArrayType) methodDeclaration.getType();
        ArrayType arrayType2 = (ArrayType) arrayType1.getComponentType();
        Assertions.assertThat(arrayType2.getComponentType()).isInstanceOf(PrimitiveType.class);

        assertThat(arrayType1.getAnnotations()).containsExactly(new MarkerAnnotationExpr(parseName("A")));
        assertThat(arrayType2.getAnnotations()).containsExactly(new MarkerAnnotationExpr(parseName("B")));
        assertThat(methodDeclaration.getAnnotations()).containsExactly(new MarkerAnnotationExpr(parseName("C")));

        assertThat(methodDeclaration.getType().getParentNode().get()).isSameAs(methodDeclaration);
    }

    @Test
    public void getParameterWithArrays() {
        MethodDeclaration methodDeclaration = (MethodDeclaration) parseClassBodyDeclaration("void a(@C int @A[] a @B[]) {};");

        Parameter parameter = methodDeclaration.getParameter(0);

        ArrayType outerArrayType = (ArrayType) parameter.getType();

        ArrayType innerArrayType = (ArrayType) outerArrayType.getComponentType();
        PrimitiveType elementType = (PrimitiveType) innerArrayType.getComponentType();

        assertThat(elementType).isInstanceOf(PrimitiveType.class);
        assertThat(outerArrayType.getAnnotations()).containsExactly(new MarkerAnnotationExpr(parseName("A")));
        assertThat(innerArrayType.getAnnotations()).containsExactly(new MarkerAnnotationExpr(parseName("B")));
        assertThat(parameter.getAnnotations()).containsExactly(new MarkerAnnotationExpr(parseName("C")));

        assertThat(parameter.getType().getParentNode().get()).isSameAs(parameter);
    }

    @Test
    public void setVariableDeclarationWithArrays() {
        ExpressionStmt variableDeclarationStatement = (ExpressionStmt) parseStatement("@C int @A[] @B[] a @X[] @Y[];");
        VariableDeclarationExpr variableDeclarationExpr = (VariableDeclarationExpr) variableDeclarationStatement.getExpression();

        variableDeclarationExpr.getVariable(0).setType(new ArrayType(new ArrayType(PrimitiveType.intType())));
        assertEquals("@C int[][] a;", variableDeclarationStatement.toString());
    }

    @Test
    public void setFieldDeclarationWithArrays() {
        FieldDeclaration fieldDeclaration = (FieldDeclaration) parseClassBodyDeclaration("int[][] a[][];");
        fieldDeclaration.getVariable(0).setType(new ArrayType(new ArrayType(new ClassOrInterfaceType("Blob"))));

        assertEquals("Blob[][] a;", fieldDeclaration.toString());
    }

    @Test
    public void setMethodDeclarationWithArrays() {
        MethodDeclaration method = (MethodDeclaration) parseClassBodyDeclaration("int[][] a()[][] {}");
        method.setType(new ArrayType(new ArrayType(new ClassOrInterfaceType("Blob"))));

        assertEquals("Blob[][] a() {" + EOL + "}", method.toString());
    }

    @Test
    public void setParameterWithArrays() {
        MethodDeclaration method = (MethodDeclaration) parseClassBodyDeclaration("void a(int[][] a[][]) {};");
        method.getParameter(0).setType(new ArrayType(new ArrayType(new ClassOrInterfaceType("Blob"))));

        assertEquals("void a(Blob[][] a) {" + EOL + "}", method.toString());
    }

    @Test
    public void getArrayCreationType() {
        ArrayCreationExpr expr = parseExpression("new int[]");
        ArrayType outerType = (ArrayType) expr.createdType();
        Type innerType = outerType.getComponentType();
        assertThat(innerType).isEqualTo(expr.getElementType());
    }
}
