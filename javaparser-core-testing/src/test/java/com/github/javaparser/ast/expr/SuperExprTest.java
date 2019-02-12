package com.github.javaparser.ast.expr;

import com.github.javaparser.ParseProblemException;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.QuickJavaParser.parseExpression;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

class SuperExprTest {
    @Test
    void justSuper() {
        assertThrows(ParseProblemException.class, () -> parseExpression("super"));
    }

    @Test
    void singleScopeSuper() {
        Expression expr = parseExpression("a.super");

        Expression classExpr = expr.asSuperExpr().getClassExpr().get();

        assertTrue(classExpr.isNameExpr());
    }

    @Test
    void multiScopeSuper() {
        Expression expr = parseExpression("a.b.super");

        Expression classExpr = expr.asSuperExpr().getClassExpr().get();

        assertTrue(classExpr.isFieldAccessExpr());
    }
}
