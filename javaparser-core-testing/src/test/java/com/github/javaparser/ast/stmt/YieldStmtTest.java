package com.github.javaparser.ast.stmt;

import com.github.javaparser.ast.expr.BinaryExpr;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.utils.TestParser.parseStatement;
import static org.junit.jupiter.api.Assertions.assertEquals;

class YieldStmtTest {
    @Test
    void yield() {
        YieldStmt statement = parseStatement("yield 12*12;").asYieldStmt();
        assertEquals(BinaryExpr.class, statement.getExpression().getClass());
    }
}