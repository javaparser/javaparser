package com.github.javaparser.ast.expr;

import org.junit.Test;

import static com.github.javaparser.JavaParser.parseExpression;
import static org.junit.Assert.*;

public class StringLiteralExprTest {
    @Test
    public void unicodeEscapesDoNotGetPreprocessed() {
        StringLiteralExpr omega = parseExpression("\"\\u03a9\"");
        assertEquals('\\', omega.getValue().charAt(0));
        assertEquals('u', omega.getValue().charAt(1));
        assertEquals('0', omega.getValue().charAt(2));
        assertEquals('3', omega.getValue().charAt(3));
        assertEquals('a', omega.getValue().charAt(4));
        assertEquals('9', omega.getValue().charAt(5));
    }
}