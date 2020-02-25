package com.github.javaparser;

import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.stmt.Statement;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Tests related to https://github.com/javaparser/javaparser/issues/2482.
 */
public class Issue2482Test {
    @Test
    public void commentBeforeLambda() {
        LambdaExpr le = StaticJavaParser.parseExpression(
                "// a comment before parent" + System.lineSeparator() +
                "()->{return 1;}");

        assertTrue(le.getComment().isPresent());
        assertTrue(le.getOrphanComments().isEmpty());
        assertEquals(0, le.getAllContainedComments().size());
    }

    @Test
    public void commentBeforeBlock() {
        Statement st = StaticJavaParser.parseBlock(
                "// a comment before parent" + System.lineSeparator() +
                "{ if (file != null) {} }");
        assertTrue(st.getComment().isPresent());
        assertTrue(st.getOrphanComments().isEmpty());
        assertEquals(0, st.getAllContainedComments().size());
    }

    @Test
    public void commentBeforeIfStatement() {
        Statement st = StaticJavaParser.parseStatement(
                "// a comment before parent" + System.lineSeparator() +
                        "if (file != null) {}");
        assertTrue(st.getComment().isPresent());
        assertTrue(st.getOrphanComments().isEmpty());
        assertEquals(0, st.getAllContainedComments().size());
    }

    @Test
    public void commentBeforeAssignment() {
        Statement st = StaticJavaParser.parseStatement(
                "// a comment" + System.lineSeparator() +
                "int x = 3;");

        assertTrue(st.getComment().isPresent());
        assertTrue(st.getOrphanComments().isEmpty());
        assertEquals(0, st.getAllContainedComments().size());
    }
}
