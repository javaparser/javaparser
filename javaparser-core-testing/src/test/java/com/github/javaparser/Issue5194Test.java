/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2026 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */
package com.github.javaparser;

import static com.github.javaparser.utils.TestParser.parseExpression;
import static org.junit.jupiter.api.Assertions.assertEquals;

import com.github.javaparser.ast.expr.CharLiteralExpr;
import com.github.javaparser.ast.expr.StringLiteralExpr;
import com.github.javaparser.ast.expr.TextBlockLiteralExpr;
import org.junit.jupiter.api.Test;

class Issue5194Test {

    @Test
    void testStringWithUnicodeEscapedBackslashN() {
        StringLiteralExpr expr = StaticJavaParser.parseExpression("\"\\u005cn\"");
        assertEquals("\n", expr.asString());
    }

    @Test
    void testStringWithUnicodeEscapedBackslashS() {
        StringLiteralExpr expr = StaticJavaParser.parseExpression("\"\\u005cs\"");
        assertEquals(" ", expr.asString());
    }

    @Test
    void testStringWithUnicodeEscapedBackslashBackslash() {
        StringLiteralExpr expr = StaticJavaParser.parseExpression("\"\\u005c\\u005c\"");
        assertEquals("\\", expr.asString());
    }

    @Test
    void testStringWithUnicodeEscapedBackslashOctal() {
        StringLiteralExpr expr = StaticJavaParser.parseExpression("\"\\u005c101\"");
        assertEquals("A", expr.asString());
    }

    @Test
    void testCharWithUnicodeEscapedBackslashN() {
        CharLiteralExpr expr = StaticJavaParser.parseExpression("'\\u005cn'");
        assertEquals('\n', expr.asChar());
    }

    @Test
    void testCharWithUnicodeEscapedBackslashS() {
        CharLiteralExpr expr = StaticJavaParser.parseExpression("'\\u005cs'");
        assertEquals(' ', expr.asChar());
    }

    @Test
    void testTextBlockWithUnicodeEscapedBackslashN() {
        TextBlockLiteralExpr expr = parseExpression("\"\"\"\na\\u005cnb\"\"\"");
        assertEquals("a\nb", expr.asString());
    }

    @Test
    void testStringWithEscapedBackslashFollowedByUnicodeEscape() {
        StringLiteralExpr expr = StaticJavaParser.parseExpression("\"\\\\u0041\"");
        assertEquals("\\u0041", expr.asString());
    }

    @Test
    void testCharWithUnicodeEscapedBackslashBackslash() {
        CharLiteralExpr expr = StaticJavaParser.parseExpression("'\\u005c\\u005c'");
        assertEquals('\\', expr.asChar());
    }

    @Test
    void testStringWithMultipleUUnicodeEscapedBackslash() {
        StringLiteralExpr expr = StaticJavaParser.parseExpression("\"\\uuuu005cn\"");
        assertEquals("\n", expr.asString());
    }

    @Test
    void testStringWithOddPrecedingBackslashesBeforeUnicodeEscape() {
        StringLiteralExpr expr = StaticJavaParser.parseExpression("\"\\\\\\u0041\"");
        assertEquals("\\A", expr.asString());
    }

    @Test
    void testStringWithEvenPrecedingBackslashesBeforeUnicodeEscape() {
        StringLiteralExpr expr = StaticJavaParser.parseExpression("\"\\\\\\\\u0041\"");
        assertEquals("\\\\u0041", expr.asString());
    }
}
