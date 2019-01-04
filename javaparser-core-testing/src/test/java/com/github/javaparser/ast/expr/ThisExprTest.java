package com.github.javaparser.ast.expr;

import org.junit.jupiter.api.Test;

import static com.github.javaparser.JavaParser.parseExpression;
import static org.junit.jupiter.api.Assertions.assertTrue;

class ThisExprTest {
    @Test
    void justThis() {
        Expression expr = parseExpression("this");

        assertTrue(expr.isThisExpr());
    }

    @Test
    void singleScopeThis() {
        Expression expr = parseExpression("a.this");

        Expression classExpr = expr.asThisExpr().getClassExpr().get();

        assertTrue(classExpr.isNameExpr());
    }

    @Test
    void multiScopeThis() {
        Expression expr = parseExpression("a.b.this");

        Expression classExpr = expr.asThisExpr().getClassExpr().get();

        assertTrue(classExpr.isFieldAccessExpr());
    }
}
