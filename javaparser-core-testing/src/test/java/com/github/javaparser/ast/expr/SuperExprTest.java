package com.github.javaparser.ast.expr;

import com.github.javaparser.ParseProblemException;
import org.junit.Test;

import static com.github.javaparser.JavaParser.getInternalParser;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class SuperExprTest {
    @Test(expected = ParseProblemException.class)
    public void justSuper() {
        getInternalParser().parseExpression("super");
    }

    @Test
    public void singleScopeSuper() {
        Expression expr = getInternalParser().parseExpression("a.super");

        Expression classExpr = expr.asSuperExpr().getClassExpr().get();

        assertTrue(classExpr.isNameExpr());
    }

    @Test
    public void multiScopeSuper() {
        Expression expr = getInternalParser().parseExpression("a.b.super");

        Expression classExpr = expr.asSuperExpr().getClassExpr().get();

        assertTrue(classExpr.isFieldAccessExpr());
    }
}
