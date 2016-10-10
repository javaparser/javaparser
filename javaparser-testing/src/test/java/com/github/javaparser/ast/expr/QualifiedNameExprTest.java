package com.github.javaparser.ast.expr;

import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class QualifiedNameExprTest {
    @Test
    public void outerNameExprIsTheRightMostIdentifier() {
        NameExpr name = NameExpr.name("a.b.c");
        assertEquals("c", name.getName());
    }

    @Test
    public void parsingAndUnparsingWorks() {
        NameExpr name = NameExpr.name("a.b.c");
        assertEquals("a.b.c", name.getQualifiedName());
    }
}