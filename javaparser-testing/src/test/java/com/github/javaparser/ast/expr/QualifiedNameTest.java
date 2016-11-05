package com.github.javaparser.ast.expr;

import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class QualifiedNameTest {
    @Test
    public void outerNameExprIsTheRightMostIdentifier() {
        Name name = Name.name("a.b.c");
        assertEquals("c", name.getName());
    }

    @Test
    public void parsingAndUnparsingWorks() {
        Name name = Name.name("a.b.c");
        assertEquals("a.b.c", name.getQualifiedName());
    }
}