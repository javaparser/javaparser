package com.github.javaparser.ast.expr;

import org.junit.Test;

import static com.github.javaparser.JavaParser.getInternalParser;
import static org.junit.Assert.*;

public class StringLiteralExprTest {
    @Test
    public void unicodeEscapesArePreservedInStrings() {
        StringLiteralExpr omega = getInternalParser().parseExpression("\"xxx\\u03a9xxx\"");
        assertEquals("xxx\\u03a9xxx", omega.getValue());
    }
}
