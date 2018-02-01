package com.github.javaparser.ast.expr;

import org.junit.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class AssignExprTest {
    @Test
    public void convertOperator() {
        assertEquals(BinaryExpr.Operator.PLUS, AssignExpr.Operator.PLUS.toBinaryOperator().get());
    }
}
