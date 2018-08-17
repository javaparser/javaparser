package com.github.javaparser;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import org.junit.Test;

import static com.github.javaparser.ParserConfiguration.LanguageLevel.BLEEDING_EDGE;
import static org.junit.Assert.*;

public class TokenRangeTest implements JavaParserSugar {
    @Override
    public <N extends Node> ParseResult<N> parse(ParseStart<N> start, Provider provider) {
        return new JavaParser(new ParserConfiguration().setLanguageLevel(BLEEDING_EDGE)).parse(start, provider);
    }

    @Test
    public void toStringWorks() {
        CompilationUnit cu = parse("class X {\n\tX(){\n// hello\n}\n}");
        assertEquals("X(){\n// hello\n}", cu.getClassByName("X").get().getDefaultConstructor().get().getTokenRange().get().toString());
    }
}