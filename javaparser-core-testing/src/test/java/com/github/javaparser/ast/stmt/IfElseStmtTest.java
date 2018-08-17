package com.github.javaparser.ast.stmt;

import com.github.javaparser.*;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import org.junit.Test;

import static com.github.javaparser.ParserConfiguration.LanguageLevel.BLEEDING_EDGE;
import static org.junit.Assert.assertEquals;

public class IfElseStmtTest implements JavaParserSugar {
    @Override
    public <N extends Node> ParseResult<N> parse(ParseStart<N> start, Provider provider) {
        return new JavaParser(new ParserConfiguration().setLanguageLevel(BLEEDING_EDGE)).parse(start, provider);
    }

    @Test
    public void issue1247withElseSingleStmt() {
        IfStmt ifStmt = (IfStmt) parseStatement("if (cond) doSomething(); else doSomethingElse();");
        assertEquals(false, ifStmt.hasElseBlock());
        assertEquals(true, ifStmt.hasElseBranch());
        assertEquals(false, ifStmt.hasCascadingIfStmt());
    }

    @Test
    public void issue1247withElseBlockStmt() {
        IfStmt ifStmt = (IfStmt) parseStatement("if (cond) doSomething(); else { doSomethingElse(); }");
        assertEquals(true, ifStmt.hasElseBlock());
        assertEquals(true, ifStmt.hasElseBranch());
        assertEquals(false, ifStmt.hasCascadingIfStmt());
    }

    @Test
    public void issue1247withElseSingleStmtWhichIsAnIf() {
        IfStmt ifStmt = (IfStmt) parseStatement("if (cond1) doSomething(); else if (cond2) doSomethingElse();");
        assertEquals(false, ifStmt.hasElseBlock());
        assertEquals(true, ifStmt.hasElseBranch());
        assertEquals(true, ifStmt.hasCascadingIfStmt());
    }

}
