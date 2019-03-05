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
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.printer.ConcreteSyntaxModel;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.*;
import static com.github.javaparser.utils.Utils.EOL;
import static org.assertj.core.api.Assertions.*;
import static org.junit.jupiter.api.Assertions.assertEquals;

class ArrayTypeTest {
    @Test
    void getFieldDeclarationWithArrays() {
        FieldDeclaration fieldDeclaration = parseBodyDeclaration("@C int @A[] @B[] a @X[] @Y[];").asFieldDeclaration();

        ArrayType arrayType1 = fieldDeclaration.getVariable(0).getType().asArrayType();
        ArrayType arrayType2 = arrayType1.getComponentType().asArrayType();
        ArrayType arrayType3 = arrayType2.getComponentType().asArrayType();
        ArrayType arrayType4 = arrayType3.getComponentType().asArrayType();
        PrimitiveType elementType = arrayType4.getComponentType().asPrimitiveType();

        assertThat(arrayType1.getAnnotations()).containsExactly(new MarkerAnnotationExpr(parseName("A")));
        assertThat(arrayType2.getAnnotations()).containsExactly(new MarkerAnnotationExpr(parseName("B")));
        assertThat(arrayType3.getAnnotations()).containsExactly(new MarkerAnnotationExpr(parseName("X")));
        assertThat(arrayType4.getAnnotations()).containsExactly(new MarkerAnnotationExpr(parseName("Y")));

        assertThat(elementType.getType()).isEqualTo(PrimitiveType.Primitive.INT);
        assertThat(fieldDeclaration.getAnnotations()).containsExactly(new MarkerAnnotationExpr(parseName("C")));

        assertThat(arrayType1.getParentNode().get().getParentNode().get()).isSameAs(fieldDeclaration);
    }

    @Test
    void getVariableDeclarationWithArrays() {
        ExpressionStmt variableDeclarationStatement = parseStatement("@C int @A[] @B[] a @X[] @Y[];").asExpressionStmt();
        VariableDeclarationExpr variableDeclarationExpr = variableDeclarationStatement.getExpression().asVariableDeclarationExpr();

        ArrayType arrayType1 = variableDeclarationExpr.getVariable(0).getType().asArrayType();
        ArrayType arrayType2 = arrayType1.getComponentType().asArrayType();
        ArrayType arrayType3 = arrayType2.getComponentType().asArrayType();
        ArrayType arrayType4 = arrayType3.getComponentType().asArrayType();
        PrimitiveType elementType = arrayType4.getComponentType().asPrimitiveType();

        assertThat(arrayType1.getAnnotations()).containsExactly(new MarkerAnnotationExpr(parseName("A")));
        assertThat(arrayType2.getAnnotations()).containsExactly(new MarkerAnnotationExpr(parseName("B")));
        assertThat(arrayType3.getAnnotations()).containsExactly(new MarkerAnnotationExpr(parseName("X")));
        assertThat(arrayType4.getAnnotations()).containsExactly(new MarkerAnnotationExpr(parseName("Y")));

        assertThat(elementType.getType()).isEqualTo(PrimitiveType.Primitive.INT);
        assertThat(variableDeclarationExpr.getAnnotations()).containsExactly(new MarkerAnnotationExpr(parseName("C")));

        assertThat(arrayType1.getParentNode().get().getParentNode().get()).isSameAs(variableDeclarationExpr);
    }

    @Test
    void getMethodDeclarationWithArrays() {
        MethodDeclaration methodDeclaration = parseBodyDeclaration("@C int @A[] a() @B[] {}").asMethodDeclaration();

        ArrayType arrayType1 = methodDeclaration.getType().asArrayType();
        ArrayType arrayType2 = arrayType1.getComponentType().asArrayType();
        Type elementType = arrayType2.getComponentType();
        assertThat(elementType).isInstanceOf(PrimitiveType.class);

        assertThat(arrayType1.getAnnotations()).containsExactly(new MarkerAnnotationExpr(parseName("A")));
        assertThat(arrayType2.getAnnotations()).containsExactly(new MarkerAnnotationExpr(parseName("B")));
        assertThat(methodDeclaration.getAnnotations()).containsExactly(new MarkerAnnotationExpr(parseName("C")));

        assertThat(methodDeclaration.getType().getParentNode().get()).isSameAs(methodDeclaration);
    }

    @Test
    void getParameterWithArrays() {
        MethodDeclaration methodDeclaration = parseBodyDeclaration("void a(@C int @A[] a @B[]) {}").asMethodDeclaration();

        Parameter parameter = methodDeclaration.getParameter(0);

        ArrayType outerArrayType = parameter.getType().asArrayType();

        ArrayType innerArrayType = outerArrayType.getComponentType().asArrayType();
        PrimitiveType elementType = innerArrayType.getComponentType().asPrimitiveType();

        assertThat(elementType).isInstanceOf(PrimitiveType.class);
        assertThat(outerArrayType.getAnnotations()).containsExactly(new MarkerAnnotationExpr(parseName("A")));
        assertThat(innerArrayType.getAnnotations()).containsExactly(new MarkerAnnotationExpr(parseName("B")));
        assertThat(parameter.getAnnotations()).containsExactly(new MarkerAnnotationExpr(parseName("C")));

        assertThat(parameter.getType().getParentNode().get()).isSameAs(parameter);
    }

    @Test
    void setVariableDeclarationWithArrays() {
        ExpressionStmt variableDeclarationStatement = parseStatement("@C int @A[] @B[] a @X[] @Y[];").asExpressionStmt();
        VariableDeclarationExpr variableDeclarationExpr = variableDeclarationStatement.getExpression().asVariableDeclarationExpr();

        variableDeclarationExpr.getVariable(0).setType(new ArrayType(new ArrayType(PrimitiveType.intType())));
        assertEquals("@C" + EOL + "int[][] a;", variableDeclarationStatement.toString());
    }

    @Test
    void setFieldDeclarationWithArrays() {
        FieldDeclaration fieldDeclaration = parseBodyDeclaration("int[][] a[][];").asFieldDeclaration();
        fieldDeclaration.getVariable(0).setType(new ArrayType(new ArrayType(parseClassOrInterfaceType("Blob"))));

        assertEquals("Blob[][] a;", fieldDeclaration.toString());
    }

    @Test
    void setMethodDeclarationWithArrays() {
        MethodDeclaration method = parseBodyDeclaration("int[][] a()[][] {}").asMethodDeclaration();
        method.setType(new ArrayType(new ArrayType(parseClassOrInterfaceType("Blob"))));

        assertEquals("Blob[][] a() {" + EOL + "}", method.toString());
    }

    @Test
    void fieldDeclarationWithArraysHasCorrectOrigins() {
        FieldDeclaration fieldDeclaration = parseBodyDeclaration("int[] a[];").asFieldDeclaration();

        Type outerType = fieldDeclaration.getVariables().get(0).getType();
        assertEquals(ArrayType.Origin.TYPE, outerType.asArrayType().getOrigin());
        assertEquals(ArrayType.Origin.NAME, outerType.asArrayType().getComponentType().asArrayType().getOrigin());
    }

    @Test
    void methodDeclarationWithArraysHasCorrectOrigins() {
        MethodDeclaration method = (MethodDeclaration) parseBodyDeclaration("int[] a()[] {}");

        Type outerType = method.getType();
        assertEquals(ArrayType.Origin.TYPE, outerType.asArrayType().getOrigin());
        assertEquals(ArrayType.Origin.NAME, outerType.asArrayType().getComponentType().asArrayType().getOrigin());
    }

    @Test
    void setParameterWithArrays() {
        MethodDeclaration method = parseBodyDeclaration("void a(int[][] a[][]) {}").asMethodDeclaration();
        method.getParameter(0).setType(new ArrayType(new ArrayType(parseClassOrInterfaceType("Blob"))));

        assertEquals("void a(Blob[][] a) {" + EOL + "}", method.toString());
    }

    @Test
    void getArrayCreationType() {
        ArrayCreationExpr expr = parseExpression("new int[]");
        ArrayType outerType = expr.createdType().asArrayType();
        Type innerType = outerType.getComponentType();
        assertThat(innerType).isEqualTo(expr.getElementType());
    }

    @Test
    void ellipsisCanHaveAnnotationsToo() {
        Parameter p = parseParameter("int[]@X...a[]");

        assertThat(p.getVarArgsAnnotations()).containsExactly(new MarkerAnnotationExpr(parseName("X")));
        assertEquals("int[][]@X ... a", p.toString());
        assertEquals("int[][]@X... a", ConcreteSyntaxModel.genericPrettyPrint(p));
    }
}
