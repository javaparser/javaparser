package com.github.javaparser.ast.expr;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

class BinaryExprTest {
    @Test
    void convertOperator() {
        assertEquals(AssignExpr.Operator.PLUS, BinaryExpr.Operator.PLUS.toAssignOperator().get());
    }
}
