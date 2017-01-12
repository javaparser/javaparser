package com.github.javaparser.ast.expr;

import org.junit.Test;

import static junit.framework.TestCase.assertEquals;

public class SimpleNameTest {

    @Test
    public void defaultConstructorSetsIdentifierToEmpty() {
        assertEquals("empty", new SimpleName().getIdentifier());
    }

    @Test(expected = AssertionError.class)
    public void identifierMustNotBeEmpty() {
        new SimpleName("");
    }

    @Test(expected = AssertionError.class)
    public void identifierMustNotBeNull() {
        new SimpleName(null);
    }

}