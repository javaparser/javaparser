package com.github.javaparser.ast.visitor;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;

public class HashCodeVisitorTest {
    @Test
    public void testEquals() {
        CompilationUnit p1 = JavaParser.parse("class X { }");
        CompilationUnit p2 = JavaParser.parse("class X { }");
        assertEquals(p1.hashCode(), p2.hashCode());
    }

    @Test
    public void testNotEquals() {
        CompilationUnit p1 = JavaParser.parse("class X { }");
        CompilationUnit p2 = JavaParser.parse("class Y { }");
        assertNotEquals(p1.hashCode(), p2.hashCode());
    }
}