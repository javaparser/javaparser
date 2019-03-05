package com.github.javaparser.ast.visitor;

import com.github.javaparser.ast.CompilationUnit;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.parse;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

class HashCodeVisitorTest {
    @Test
    void testEquals() {
        CompilationUnit p1 = parse("class X { }");
        CompilationUnit p2 = parse("class X { }");
        assertEquals(p1.hashCode(), p2.hashCode());
    }

    @Test
    void testNotEquals() {
        CompilationUnit p1 = parse("class X { }");
        CompilationUnit p2 = parse("class Y { }");
        assertNotEquals(p1.hashCode(), p2.hashCode());
    }
}