package com.github.javaparser.ast.visitor;

import com.github.javaparser.*;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import org.junit.Test;

import static com.github.javaparser.ParserConfiguration.LanguageLevel.BLEEDING_EDGE;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;

public class HashCodeVisitorTest implements JavaParserSugar {
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
    public void testNotEquals() {
        CompilationUnit p1 = parse("class X { }");
        CompilationUnit p2 = parse("class Y { }");
        assertNotEquals(p1.hashCode(), p2.hashCode());
    }
}