package com.github.javaparser.ast.stmt;

import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.parseStatement;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

class IfElseStmtTest {

    @Test
    void issue1247withElseSingleStmt() {
        IfStmt ifStmt = parseStatement("if (cond) doSomething(); else doSomethingElse();").asIfStmt();
        assertFalse(ifStmt.hasElseBlock());
        assertTrue(ifStmt.hasElseBranch());
        assertFalse(ifStmt.hasCascadingIfStmt());
    }

    @Test
    void issue1247withElseBlockStmt() {
        IfStmt ifStmt = parseStatement("if (cond) doSomething(); else { doSomethingElse(); }").asIfStmt();
        assertTrue(ifStmt.hasElseBlock());
        assertTrue(ifStmt.hasElseBranch());
        assertFalse(ifStmt.hasCascadingIfStmt());
    }

    @Test
    void issue1247withElseSingleStmtWhichIsAnIf() {
        IfStmt ifStmt = parseStatement("if (cond1) doSomething(); else if (cond2) doSomethingElse();").asIfStmt();
        assertFalse(ifStmt.hasElseBlock());
        assertTrue(ifStmt.hasElseBranch());
        assertTrue(ifStmt.hasCascadingIfStmt());
    }

}
