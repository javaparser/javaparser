package com.github.javaparser.ast.expr;

import com.github.javaparser.ParseProblemException;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.parseExpression;
import static org.junit.jupiter.api.Assertions.*;
import static org.junit.jupiter.api.Assertions.assertEquals;

class SuperExprTest {
    @Test
    void justSuper() {
        assertThrows(ParseProblemException.class, () -> parseExpression("super"));
    }

    @Test
    void singleScopeSuper() {
        Expression expr = parseExpression("A.super");

        Name className = expr.asSuperExpr().getTypeName().get();

        assertEquals("A", className.asString());
    }

    @Test
    void multiScopeSuper() {
        Expression expr = parseExpression("a.B.super");

        Name className = expr.asSuperExpr().getTypeName().get();

        assertEquals("a.B", className.asString());
    }
}
