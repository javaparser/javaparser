package com.github.javaparser.ast.stmt;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class IfElseStmtTest {

    @Test
    public void issue1247withElseSingleStmt() {
        IfStmt ifStmt = (IfStmt) JavaParser.parseStatement("if (cond) doSomething(); else doSomethingElse();");
        assertEquals(false, ifStmt.hasElseBlock());
        assertEquals(true, ifStmt.hasElseBranch());
        assertEquals(false, ifStmt.hasCascadingIfStmt());
    }

    @Test
    public void issue1247withElseBlockStmt() {
        IfStmt ifStmt = (IfStmt) JavaParser.parseStatement("if (cond) doSomething(); else { doSomethingElse(); }");
        assertEquals(true, ifStmt.hasElseBlock());
        assertEquals(true, ifStmt.hasElseBranch());
        assertEquals(false, ifStmt.hasCascadingIfStmt());
    }

    @Test
    public void issue1247withElseSingleStmtWhichIsAnIf() {
        IfStmt ifStmt = (IfStmt) JavaParser.parseStatement("if (cond1) doSomething(); else if (cond2) doSomethingElse();");
        assertEquals(false, ifStmt.hasElseBlock());
        assertEquals(true, ifStmt.hasElseBranch());
        assertEquals(true, ifStmt.hasCascadingIfStmt());
    }

}
