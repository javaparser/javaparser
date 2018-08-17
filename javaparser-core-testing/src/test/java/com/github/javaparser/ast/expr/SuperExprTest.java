package com.github.javaparser.ast.expr;

import com.github.javaparser.ParseProblemException;
import org.junit.Test;

import static com.github.javaparser.JavaParser.parseExpression;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class SuperExprTest {
    @Test(expected = ParseProblemException.class)
    public void justSuper() {
        parseExpression("super");
    }

    @Test
    public void singleScopeSuper() {
        Expression expr = parseExpression("a.super");

        Expression classExpr = expr.asSuperExpr().getClassExpr().get();

        assertTrue(classExpr.isNameExpr());
    }

    @Test
    public void multiScopeSuper() {
        Expression expr = parseExpression("a.b.super");

        Expression classExpr = expr.asSuperExpr().getClassExpr().get();

        assertTrue(classExpr.isFieldAccessExpr());
    }
}
