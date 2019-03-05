package com.github.javaparser.ast.expr;

import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.parseExpression;
import static org.junit.jupiter.api.Assertions.*;

class StringLiteralExprTest {
    @Test
    void unicodeEscapesArePreservedInStrings() {
        StringLiteralExpr omega = parseExpression("\"xxx\\u03a9xxx\"");
        assertEquals("xxx\\u03a9xxx", omega.getValue());
    }
}
