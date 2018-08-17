package com.github.javaparser.ast.expr;

import com.github.javaparser.*;
import com.github.javaparser.ast.Node;
import org.junit.Test;

import static com.github.javaparser.ParserConfiguration.LanguageLevel.BLEEDING_EDGE;
import static org.assertj.core.api.AssertionsForInterfaceTypes.assertThat;

public class InstanceOfExprTest implements JavaParserSugar {
    @Override
    public <N extends Node> ParseResult<N> parse(ParseStart<N> start, Provider provider) {
        return new JavaParser(new ParserConfiguration().setLanguageLevel(BLEEDING_EDGE)).parse(start, provider);
    }

    @Test
    public void annotationsOnTheType() {
        InstanceOfExpr expr = parseExpression("s instanceof @A @DA String");

        assertThat(expr.getType().getAnnotations()).containsExactly(new MarkerAnnotationExpr("A"), new MarkerAnnotationExpr("DA"));
    }
}
