package com.github.javaparser.ast.expr;

import org.junit.Test;

import static org.junit.Assert.assertTrue;

public class MethodReferenceTest {

    @Test
    public void methodReferenceExprHasAlwaysAScope() {
        assertTrue(new MethodReferenceExpr().getScope() != null);
    }

}
