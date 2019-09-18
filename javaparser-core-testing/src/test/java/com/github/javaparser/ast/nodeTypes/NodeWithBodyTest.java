package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.stmt.ForStmt;
import com.github.javaparser.ast.stmt.IfStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.utils.TestParser;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class NodeWithBodyTest {
    @Test
    void emptyStatementIsEmpty() {
        ForStmt forStmt = TestParser.parseStatement("for(;;);").asForStmt();

        assertTrue(forStmt.hasEmptyBody());
    }

    @Test
    void emptyBlockIsEmpty() {
        ForStmt forStmt = TestParser.parseStatement("for(;;){}").asForStmt();

        assertTrue(forStmt.hasEmptyBody());
    }

    @Test
    void simpleStatementIsNotEmpty() {
        ForStmt forStmt = TestParser.parseStatement("for(;;)a=b;").asForStmt();

        assertFalse(forStmt.hasEmptyBody());
    }

    @Test
    void nonEmptyBlockIsNotEmpty() {
        ForStmt forStmt = TestParser.parseStatement("for(;;){a=b;}").asForStmt();

        assertFalse(forStmt.hasEmptyBody());
    }
}