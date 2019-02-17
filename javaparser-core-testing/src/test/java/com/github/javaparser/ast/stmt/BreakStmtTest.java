package com.github.javaparser.ast.stmt;

import com.github.javaparser.ast.expr.BinaryExpr;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.parseStatement;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

class BreakStmtTest {
    @Test
    void simpleBreak() {
        BreakStmt statement = parseStatement("break;").asBreakStmt();
        assertFalse(statement.getValue().isPresent());
    }

    @Test
    void breakWithLabel() {
        BreakStmt statement = parseStatement("break hond;").asBreakStmt();
        assertEquals("hond", statement.getValue().get().asNameExpr().getName().asString());

    }

    @Test
    void breakWithExpression() {
        BreakStmt statement = parseStatement("break 12*12;").asBreakStmt();
        assertEquals(BinaryExpr.class, statement.getValue().get().getClass());
    }
}