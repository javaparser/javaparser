package com.github.javaparser.ast.expr;

import org.junit.Test;

import static com.github.javaparser.JavaParser.parseExpression;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class ThisExprTest {
    @Test
    public void justThis() {
        Expression expr = parseExpression("this");

        assertTrue(expr.isThisExpr());
    }

    @Test
    public void singleScopeThis() {
        Expression expr = parseExpression("a.this");

        Expression classExpr = expr.asThisExpr().getClassExpr().get();

        assertTrue(classExpr.isNameExpr());
    }

    @Test
    public void multiScopeThis() {
        Expression expr = parseExpression("a.b.this");

        Expression classExpr = expr.asThisExpr().getClassExpr().get();

        assertTrue(classExpr.isFieldAccessExpr());
    }
}
