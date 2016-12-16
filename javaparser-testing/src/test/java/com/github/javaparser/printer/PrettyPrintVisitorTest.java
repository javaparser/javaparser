package com.github.javaparser.printer;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import org.junit.Test;

import static com.github.javaparser.printer.PrettyPrintVisitor.getMaximumCommonType;
import static org.junit.Assert.assertEquals;

public class PrettyPrintVisitorTest {

    @Test
    public void getMaximumCommonTypeWithoutAnnotations() {
        VariableDeclarationExpr vde1 = JavaParser.parseVariableDeclarationExpr("int a[], b[]");
        assertEquals("int[]", getMaximumCommonType(vde1).toString());

        VariableDeclarationExpr vde2 = JavaParser.parseVariableDeclarationExpr("int[][] a[], b[]");
        assertEquals("int[][][]", getMaximumCommonType(vde2).toString());

        VariableDeclarationExpr vde3 = JavaParser.parseVariableDeclarationExpr("int[][] a, b[]");
        assertEquals("int[][]", getMaximumCommonType(vde3).toString());
    }

    @Test
    public void getMaximumCommonTypeWithAnnotations() {
        VariableDeclarationExpr vde1 = JavaParser.parseVariableDeclarationExpr("int a @Foo [], b[]");
        assertEquals("int", getMaximumCommonType(vde1).toString());

        VariableDeclarationExpr vde2 = JavaParser.parseVariableDeclarationExpr("int[]@Foo [] a[], b[]");
        assertEquals("int[] @Foo [][]", getMaximumCommonType(vde2).toString());
    }
}
