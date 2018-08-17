package com.github.javaparser.ast.expr;

import org.junit.Test;

import static com.github.javaparser.JavaParser.getInternalParser;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class ThisExprTest {
    @Test
    public void justThis() {
        Expression expr = getInternalParser().parseExpression("this");

        assertTrue(expr.isThisExpr());
    }

    @Test
    public void singleScopeThis() {
        Expression expr = getInternalParser().parseExpression("a.this");

        Expression classExpr = expr.asThisExpr().getClassExpr().get();

        assertTrue(classExpr.isNameExpr());
    }

    @Test
    public void multiScopeThis() {
        Expression expr = getInternalParser().parseExpression("a.b.this");

        Expression classExpr = expr.asThisExpr().getClassExpr().get();

        assertTrue(classExpr.isFieldAccessExpr());
    }
}
