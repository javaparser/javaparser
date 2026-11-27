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

package com.github.javaparser.ast.expr;

import static com.github.javaparser.Providers.provider;
import static org.junit.jupiter.api.Assertions.assertEquals;

import com.github.javaparser.JavaParser;
import com.github.javaparser.JavaParserAdapter;
import com.github.javaparser.ParseStart;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import org.junit.jupiter.api.Test;

class CharLiteralExprTest {

    private final JavaParserAdapter parser = StaticJavaParser.newParserAdapter();

    @Test
    void parseSimpleChar() {
        CharLiteralExpr c = parser.parseExpression("'a'");
        assertEquals("a", c.getValue());
    }

    @Test
    void parseSimpleEscape() {
        CharLiteralExpr c = parser.parseExpression("'\\t'");
        assertEquals("\\t", c.getValue());
    }

    @Test
    void parseUnicode() {
        CharLiteralExpr c = parser.parseExpression("'Ω'");
        assertEquals("Ω", c.getValue());
    }

    @Test
    void parseNumericEscape() {
        CharLiteralExpr c = parser.parseExpression("'\\177'");
        assertEquals("\\177", c.getValue());
    }

    @Test
    void parseUnicodeEscape() {
        CharLiteralExpr c = parser.parseExpression("'\\u03a9'");
        assertEquals("\\u03a9", c.getValue());
    }

    @Test
    void parseUnicodeEscapedEscape() {
        JavaParser javaParser = new JavaParser(new ParserConfiguration().setPreprocessUnicodeEscapes(true));

        CharLiteralExpr c = javaParser
                .parse(ParseStart.EXPRESSION, provider("'\\u005c''"))
                .getResult()
                .get()
                .asCharLiteralExpr();
        assertEquals("\\'", c.getValue());
    }

    @Test
    void spaceEscapeIsTranslated() {
        // JLS 3.10.7: \s is an escape sequence for a space in character literals too
        CharLiteralExpr c = parser.parseExpression("'\\s'");
        assertEquals("\\s", c.getValue());
        assertEquals(' ', c.asChar());
    }

    @Test
    void charLiteralConstructorEscapesSpecialChars() {
        CharLiteralExpr singleQuote = new CharLiteralExpr('\'');
        assertEquals("\\'", singleQuote.getValue());
        assertEquals('\'', singleQuote.asChar());
        assertEquals("'\\''", singleQuote.toString());
        assertEquals(singleQuote, StaticJavaParser.parseExpression(singleQuote.toString()));

        CharLiteralExpr backslash = new CharLiteralExpr('\\');
        assertEquals("\\\\", backslash.getValue());
        assertEquals('\\', backslash.asChar());
        assertEquals("'\\\\'", backslash.toString());
        assertEquals(backslash, StaticJavaParser.parseExpression(backslash.toString()));

        CharLiteralExpr newline = new CharLiteralExpr('\n');
        assertEquals("\\n", newline.getValue());
        assertEquals('\n', newline.asChar());
        assertEquals("'\\n'", newline.toString());
        assertEquals(newline, StaticJavaParser.parseExpression(newline.toString()));

        CharLiteralExpr tab = new CharLiteralExpr('\t');
        assertEquals("\\t", tab.getValue());
        assertEquals('\t', tab.asChar());
        assertEquals("'\\t'", tab.toString());
        assertEquals(tab, StaticJavaParser.parseExpression(tab.toString()));
    }

    @Test
    void charLiteralSetterEscapesSpecialChars() {
        CharLiteralExpr c = new CharLiteralExpr('a');

        c.setChar('\'');
        assertEquals("\\'", c.getValue());
        assertEquals('\'', c.asChar());
        assertEquals("'\\''", c.toString());
        assertEquals(c, StaticJavaParser.parseExpression(c.toString()));

        c.setChar('\\');
        assertEquals("\\\\", c.getValue());
        assertEquals('\\', c.asChar());
        assertEquals("'\\\\'", c.toString());
        assertEquals(c, StaticJavaParser.parseExpression(c.toString()));

        c.setChar('\n');
        assertEquals("\\n", c.getValue());
        assertEquals('\n', c.asChar());
        assertEquals("'\\n'", c.toString());
        assertEquals(c, StaticJavaParser.parseExpression(c.toString()));

        c.setChar('\t');
        assertEquals("\\t", c.getValue());
        assertEquals('\t', c.asChar());
        assertEquals("'\\t'", c.toString());
        assertEquals(c, StaticJavaParser.parseExpression(c.toString()));
    }
}
