package com.github.javaparser.ast.expr;

import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.parseExpression;
import static org.assertj.core.api.AssertionsForInterfaceTypes.assertThat;

class InstanceOfExprTest {
    @Test
    void annotationsOnTheType() {
        InstanceOfExpr expr = parseExpression("s instanceof @A @DA String");

        assertThat(expr.getType().getAnnotations()).containsExactly(new MarkerAnnotationExpr("A"), new MarkerAnnotationExpr("DA"));
    }
}
