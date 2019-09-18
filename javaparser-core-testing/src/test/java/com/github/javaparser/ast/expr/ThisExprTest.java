package com.github.javaparser.ast.expr;

import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.parseExpression;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

class ThisExprTest {
    @Test
    void justThis() {
        Expression expr = parseExpression("this");

        assertTrue(expr.isThisExpr());
    }

    @Test
    void singleScopeThis() {
        Expression expr = parseExpression("A.this");

        Name className = expr.asThisExpr().getTypeName().get();

        assertEquals("A", className.asString());
    }

    @Test
    void multiScopeThis() {
        Expression expr = parseExpression("a.B.this");

        Name className = expr.asThisExpr().getTypeName().get();

        assertEquals("a.B", className.asString());
    }
}
