package com.github.javaparser.ast.expr;

import org.junit.Test;

import static com.github.javaparser.JavaParser.parseExpression;
import static org.junit.Assert.*;

public class StringLiteralExprTest {
    @Test
    public void unicodeEscapesArePreservedInStrings() {
        StringLiteralExpr omega = parseExpression("\"xxx\\u03a9xxx\"");
        assertEquals("xxx\\u03a9xxx", omega.getValue());
    }
}
