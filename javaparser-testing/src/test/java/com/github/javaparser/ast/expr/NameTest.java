package com.github.javaparser.ast.expr;

import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class NameTest {
    @Test
    public void outerNameExprIsTheRightMostIdentifier() {
        Name name = Name.parse("a.b.c");
        assertEquals("c", name.getId());
    }

    @Test
    public void parsingAndUnparsingWorks() {
        Name name = Name.parse("a.b.c");
        assertEquals("a.b.c", name.asString());
    }
}