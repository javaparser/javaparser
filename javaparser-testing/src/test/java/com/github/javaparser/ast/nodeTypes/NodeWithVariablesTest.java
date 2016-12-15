package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.type.PrimitiveType;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class NodeWithVariablesTest {

    @Test
    public void getCommonTypeWorksForNormalVariables() {
        VariableDeclarationExpr declaration = JavaParser.parseVariableDeclarationExpr("int a,b;");
        assertEquals(PrimitiveType.INT_TYPE, declaration.getCommonType());
    }

    @Test
    public void getCommonTypeWorksForArrayTypes() {
        JavaParser.parseVariableDeclarationExpr("int a[],b[];").getCommonType();
    }

    @Test(expected = AssertionError.class)
    public void getCommonTypeFailsOnArrayDifferences() {
        JavaParser.parseVariableDeclarationExpr("int a[],b[][];").getCommonType();
    }

    @Test(expected = AssertionError.class)
    public void getCommonTypeFailsOnDodgySetterUsage() {
        VariableDeclarationExpr declaration = JavaParser.parseVariableDeclarationExpr("int a,b;");
        declaration.getVariable(1).setType(String.class);
        declaration.getCommonType();
    }

    @Test(expected = AssertionError.class)
    public void getCommonTypeFailsOnInvalidEmptyVariableList() {
        VariableDeclarationExpr declaration = JavaParser.parseVariableDeclarationExpr("int a;");
        declaration.getVariables().clear();
        declaration.getCommonType();
    }

    @Test
    public void getElementTypeWorksForNormalVariables() {
        VariableDeclarationExpr declaration = JavaParser.parseVariableDeclarationExpr("int a,b;");
        assertEquals(PrimitiveType.INT_TYPE, declaration.getElementType());
    }

    @Test
    public void getElementTypeWorksForArrayTypes() {
        VariableDeclarationExpr declaration = JavaParser.parseVariableDeclarationExpr("int a[],b[];");
        assertEquals(PrimitiveType.INT_TYPE, declaration.getElementType());
    }

    @Test
    public void getElementTypeIsOkayWithArrayDifferences() {
        JavaParser.parseVariableDeclarationExpr("int a[],b[][];").getElementType();
    }

    @Test(expected = AssertionError.class)
    public void getElementTypeFailsOnDodgySetterUsage() {
        VariableDeclarationExpr declaration = JavaParser.parseVariableDeclarationExpr("int a,b;");
        declaration.getVariable(1).setType(String.class);
        declaration.getElementType();
    }

    @Test(expected = AssertionError.class)
    public void getElementTypeFailsOnInvalidEmptyVariableList() {
        VariableDeclarationExpr declaration = JavaParser.parseVariableDeclarationExpr("int a;");
        declaration.getVariables().clear();
        declaration.getElementType();
    }

    @Test
    public void getMaximumCommonTypeWithoutAnnotations() {
        VariableDeclarationExpr vde1 = JavaParser.parseVariableDeclarationExpr("int a[], b[]");
        assertEquals("int[]", vde1.getMaximumCommonType().toString());

        VariableDeclarationExpr vde2 = JavaParser.parseVariableDeclarationExpr("int[][] a[], b[]");
        assertEquals("int[][][]", vde2.getMaximumCommonType().toString());

        VariableDeclarationExpr vde3 = JavaParser.parseVariableDeclarationExpr("int[][] a, b[]");
        assertEquals("int[][]", vde3.getMaximumCommonType().toString());
    }

    @Test
    public void getMaximumCommonTypeWithAnnotations() {
        VariableDeclarationExpr vde1 = JavaParser.parseVariableDeclarationExpr("int a @Foo [], b[]");
        assertEquals("int", vde1.getMaximumCommonType().toString());

        VariableDeclarationExpr vde2 = JavaParser.parseVariableDeclarationExpr("int[]@Foo [] a[], b[]");
        assertEquals("int[] @Foo [][]", vde2.getMaximumCommonType().toString());
    }
}