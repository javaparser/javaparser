package com.github.javaparser.ast.visitor;

import com.github.javaparser.ast.CompilationUnit;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.parse;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

class NoCommentHashCodeVisitorTest {

    @Test
    void testEquals() {
        CompilationUnit p1 = parse("class X { }");
        CompilationUnit p2 = parse("class X { }");
        assertEquals(p1.hashCode(), p2.hashCode());
    }

    @Test
    void testEqualsWithDifferentComments() {
        CompilationUnit p1 = parse("/* a */ class X { /** b */} //c");
        CompilationUnit p2 = parse("/* b */ class X { }  //c");
        assertEquals(p1.hashCode(), p2.hashCode());
        assertEquals(p1.getComments().size(), 3);
        assertEquals(p2.getComments().size(), 2);
    }

    @Test
    void testNotEquals() {
        CompilationUnit p1 = parse("class X { }");
        CompilationUnit p2 = parse("class Y { }");
        assertNotEquals(p1.hashCode(), p2.hashCode());
    }
}