package com.github.javaparser.ast.visitor;

import com.github.javaparser.*;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import org.junit.Test;

import static com.github.javaparser.ParserConfiguration.LanguageLevel.BLEEDING_EDGE;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;

public class NoCommentHashCodeVisitorTest implements JavaParserSugar {
    @Override
    public <N extends Node> ParseResult<N> parse(ParseStart<N> start, Provider provider) {
        return new JavaParser(new ParserConfiguration().setLanguageLevel(BLEEDING_EDGE)).parse(start, provider);
    }

    @Test
    public void testEquals() {
        CompilationUnit p1 = parse("class X { }");
        CompilationUnit p2 = parse("class X { }");
        assertEquals(p1.hashCode(), p2.hashCode());
    }

    @Test
    public void testEqualsWithDifferentComments() {
        CompilationUnit p1 = parse("/* a */ class X { /** b */} //c");
        CompilationUnit p2 = parse("/* b */ class X { }  //c");
        assertEquals(p1.hashCode(), p2.hashCode());
        assertEquals(p1.getComments().size(), 3);
        assertEquals(p2.getComments().size(), 2);
    }

    @Test
    public void testNotEquals() {
        CompilationUnit p1 = parse("class X { }");
        CompilationUnit p2 = parse("class Y { }");
        assertNotEquals(p1.hashCode(), p2.hashCode());
    }
}