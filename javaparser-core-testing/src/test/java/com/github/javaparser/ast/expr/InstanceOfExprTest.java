package com.github.javaparser.ast.expr;

import com.github.javaparser.JavaParser;
import org.junit.jupiter.api.Test;

import static org.assertj.core.api.AssertionsForInterfaceTypes.assertThat;

class InstanceOfExprTest {
    @Test
    void annotationsOnTheType() {
        InstanceOfExpr expr = JavaParser.parseExpression("s instanceof @A @DA String");

        assertThat(expr.getType().getAnnotations()).containsExactly(new MarkerAnnotationExpr("A"), new MarkerAnnotationExpr("DA"));
    }
}
