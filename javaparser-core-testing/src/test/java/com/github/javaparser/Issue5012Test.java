/*
 * Copyright (C) 2013-2026 The JavaParser Team.
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

import static com.github.javaparser.StaticJavaParser.parseExpression;
import static com.github.javaparser.StaticJavaParser.parseSimpleName;
import static com.github.javaparser.utils.TestUtils.assertNoProblems;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.CharLiteralExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.expr.StringLiteralExpr;
import org.junit.jupiter.api.Test;

/**
 * Issue #5012: Lexical error when parsing Unicode escapes with multiple 'u' characters.
 *
 * <p>JLS §3.3 defines {@code UnicodeMarker} as {@code u {u}}, i.e. one or more {@code u}
 * characters after the backslash are valid.
 */
public class Issue5012Test {

    @Test
    void parseStringWithMultipleUUnicodeEscape() {
        StringLiteralExpr expr = parseExpression("\"t\\uuuu1234\"");
        assertEquals("t\\uuuu1234", expr.getValue());
    }

    @Test
    void parseStringWithSingleUUnicodeEscape() {
        StringLiteralExpr expr = parseExpression("\"t\\u1234\"");
        assertEquals("t\\u1234", expr.getValue());
    }

    @Test
    void parseCharWithMultipleUUnicodeEscape() {
        CharLiteralExpr expr = parseExpression("'\\uuuu1234'");
        assertEquals("\\uuuu1234", expr.getValue());
    }

    @Test
    void parseIdentifierWithMultipleUUnicodeEscape() {
        SimpleName name = parseSimpleName("xxx\\uuu2122xxx");
        assertEquals("xxx\\uuu2122xxx", name.asString());
    }

    @Test
    void parseCompilationUnitWithMultipleUUnicodeEscapes() {
        String code = "public class UnicodeTest {\n"
                + "    private String s1 = \"t\\u1234\";\n"
                + "    private String s2 = \"t\\uuuu1234\";\n"
                + "    private char c = '\\uuu0041';\n"
                + "}\n";

        ParserConfiguration configuration = new ParserConfiguration();
        configuration.setLanguageLevel(ParserConfiguration.LanguageLevel.BLEEDING_EDGE);
        JavaParser parser = new JavaParser(configuration);
        ParseResult<CompilationUnit> result = parser.parse(code);

        assertTrue(result.isSuccessful(), () -> "Expected successful parse, problems: " + result.getProblems());
        assertNoProblems(result);
    }

    @Test
    void parseCompilationUnitWithMultipleUUnicodeEscapesAndPreprocess() {
        String code = "public class UnicodeTest {\n"
                + "    private String s1 = \"t\\u1234\";\n"
                + "    private String s2 = \"t\\uuuu1234\";\n"
                + "}\n";

        ParserConfiguration configuration = new ParserConfiguration();
        configuration.setLanguageLevel(ParserConfiguration.LanguageLevel.BLEEDING_EDGE);
        configuration.setPreprocessUnicodeEscapes(true);
        JavaParser parser = new JavaParser(configuration);
        ParseResult<CompilationUnit> result = parser.parse(code);

        assertTrue(result.isSuccessful(), () -> "Expected successful parse, problems: " + result.getProblems());
        assertNoProblems(result);
    }
}
