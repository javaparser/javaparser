package com.github.javaparser.ast.expr;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

class AssignExprTest {
    @Test
    void convertOperator() {
        assertEquals(BinaryExpr.Operator.PLUS, AssignExpr.Operator.PLUS.toBinaryOperator().get());
    }
}
