package com.github.javaparser.ast.expr;

import org.junit.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class BinaryExprTest {
    @Test
    public void convertOperator() {
        assertEquals(AssignExpr.Operator.PLUS, BinaryExpr.Operator.PLUS.toAssignOperator().get());
    }
}
