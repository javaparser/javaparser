package com.github.javaparser.ast.stmt;

import org.junit.jupiter.api.Test;

import static com.github.javaparser.utils.TestParser.parseStatement;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

class BreakStmtTest {
    @Test
    void simpleBreak() {
        BreakStmt statement = parseStatement("break;").asBreakStmt();
        assertFalse(statement.getLabel().isPresent());
    }

    @Test
    void breakWithLabel() {
        BreakStmt statement = parseStatement("break hond;").asBreakStmt();
        assertEquals("hond", statement.getLabel().get().asString());
    }
}