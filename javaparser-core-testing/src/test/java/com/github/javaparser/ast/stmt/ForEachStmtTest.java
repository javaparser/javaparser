package com.github.javaparser.ast.stmt;

import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.PrimitiveType;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.parseStatement;
import static org.junit.jupiter.api.Assertions.*;

class ForEachStmtTest {
    @Test
    void nonFinalPrimitive() {
        ForEachStmt statement = parseStatement("for (int i : ints) {}").asForEachStmt();
        assertFalse(statement.hasFinalVariable());
        assertEquals(PrimitiveType.intType(), statement.getVariableDeclarator().getType());
        assertEquals("i", statement.getVariableDeclarator().getName().getIdentifier());
    }

    @Test
    void finalNonPrimitive() {
        ForEachStmt statement = parseStatement("for (final Object o : objs) {}").asForEachStmt();
        assertTrue(statement.hasFinalVariable());
        assertEquals(new ClassOrInterfaceType(null, "Object"), statement.getVariableDeclarator().getType());
        assertEquals("o", statement.getVariableDeclarator().getName().getIdentifier());
    }
}
