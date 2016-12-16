package com.github.javaparser.printer;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class PrettyPrinterTest {
    CompilationUnit cu;

    @Before
    public void setUp() {
        cu = new CompilationUnit();
    }

    @After
    public void teardown() {
        cu = null;
    }

    private String prettyPrintField(String code) {
        CompilationUnit cu = JavaParser.parse(code);
        return new PrettyPrinter().print(cu.getNodesByType(FieldDeclaration.class).get(0));
    }

    private String prettyPrintVar(String code) {
        CompilationUnit cu = JavaParser.parse(code);
        return new PrettyPrinter().print(cu.getNodesByType(VariableDeclarationExpr.class).get(0));
    }

    @Test
    public void printingArrayFields() {
        String code;
        code = "class A { int a, b[]; }";
        assertEquals("int a, b[];", prettyPrintField(code));

        code = "class A { int[] a[], b[]; }";
        assertEquals("int[][] a, b;", prettyPrintField(code));

        code = "class A { int[] a[][], b; }";
        assertEquals("int[] a[][], b;", prettyPrintField(code));

        code = "class A { int[] a, b; }";
        assertEquals("int[] a, b;", prettyPrintField(code));

        code = "class A { int a[], b[]; }";
        assertEquals("int[] a, b;", prettyPrintField(code));
    }

    @Test
    public void printingArrayVariables() {
        String code;
        code = "class A { void foo(){ int a, b[]; }}";
        assertEquals("int a, b[]", prettyPrintVar(code));

        code = "class A { void foo(){ int[] a[], b[]; }}";
        assertEquals("int[][] a, b", prettyPrintVar(code));

        code = "class A { void foo(){ int[] a[][], b; }}";
        assertEquals("int[] a[][], b", prettyPrintVar(code));

        code = "class A { void foo(){ int[] a, b; }}";
        assertEquals("int[] a, b", prettyPrintVar(code));

        code = "class A { void foo(){ int a[], b[]; }}";
        assertEquals("int[] a, b", prettyPrintVar(code));
    }

}
