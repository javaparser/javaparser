package com.github.javaparser.ast.type;

import org.junit.Test;

import static com.github.javaparser.JavaParser.parseVariableDeclarationExpr;
import static org.junit.Assert.assertEquals;

public class TypeTest {
    @Test
    public void asString() {
        assertEquals("int", typeAsString("int x;"));
        assertEquals("List<Long>", typeAsString("List<Long> x;"));
        assertEquals("String", typeAsString("@A String x;"));
        assertEquals("List<? extends Object>", typeAsString("List<? extends Object> x;"));
    }

    private String typeAsString(String s) {
        return parseVariableDeclarationExpr(s).getVariable(0).getType().asString();
    }
}
