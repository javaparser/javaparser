package com.github.javaparser.ast.expr;

import com.github.javaparser.utils.TestParser;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

class ObjectCreationExprTest {
    @Test
    void aaa() {
        Expression e = TestParser.parseExpression("new @Test N()");
        assertEquals("new @Test N()", e.toString());
    }
}