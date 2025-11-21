/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2025 The JavaParser Team.
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

package com.github.javaparser.ast.validator;

import static com.github.javaparser.ParseStart.COMPILATION_UNIT;
import static com.github.javaparser.ParserConfiguration.LanguageLevel.JAVA_25;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.utils.TestUtils.assertNoProblems;
import static com.github.javaparser.utils.TestUtils.assertProblems;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import org.junit.jupiter.api.Test;

/**
 * Tests for JEP 513: Flexible Constructor Bodies
 */
public class FlexibleConstructorTest {

    private final JavaParser javaParser = new JavaParser(new ParserConfiguration().setLanguageLevel(JAVA_25));

    // ==================== Valid Cases ====================

    @Test
    void validationBeforeSuperCall() {
        String code = "class Example {\n" +
                "    Example(int value) {\n" +
                "        if (value < 0) {\n" +
                "            throw new IllegalArgumentException();\n" +
                "        }\n" +
                "        super();\n" +
                "    }\n" +
                "}";
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(code));
        assertNoProblems(result);
    }

    @Test
    void fieldInitializationBeforeSuperCall() {
        String code = "class Example {\n" +
                "    private final int value;\n" +
                "    Example(int v) {\n" +
                "        value = v * 2;\n" +
                "        super();\n" +
                "    }\n" +
                "}";
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(code));
        assertNoProblems(result);
    }

    @Test
    void multipleStatementsBeforeSuperCall() {
        String code = "class Example {\n" +
                "    Example(String s) {\n" +
                "        int len = s.length();\n" +
                "        if (len > 100) {\n" +
                "            s = s.substring(0, 100);\n" +
                "        }\n" +
                "        super();\n" +
                "    }\n" +
                "}";
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(code));
        assertNoProblems(result);
    }

    @Test
    void statementsBeforeThisCall() {
        String code = "class Example {\n" +
                "    Example() { }\n" +
                "    Example(int value) {\n" +
                "        if (value < 0) {\n" +
                "            value = 0;\n" +
                "        }\n" +
                "        this();\n" +
                "    }\n" +
                "}";
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(code));
        assertNoProblems(result);
    }

    @Test
    void statementsAfterSuperCall() {
        String code = "class Example {\n" +
                "    Example() {\n" +
                "        super();\n" +
                "        System.out.println(\"Constructed\");\n" +
                "    }\n" +
                "}";
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(code));
        assertNoProblems(result);
    }

    @Test
    void constructorWithoutExplicitCall() {
        // No super/this call - prologue validation doesn't apply
        String code = "class Example {\n" +
                "    Example() {\n" +
                "        System.out.println(this);\n" +
                "    }\n" +
                "}";
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(code));
        assertNoProblems(result);
    }

    // ==================== Invalid Cases ====================

    @Test
    void thisReferenceInPrologueNotAllowed() {
        String code = "class Example {\n" +
                "    Example() {\n" +
                "        System.out.println(this);\n" +
                "        super();\n" +
                "    }\n" +
                "}";
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(code));
        assertProblems(result, "(line 3,col 9) Statements before super() or this() cannot reference the current instance ('this').");
    }

    @Test
    void thisMethodCallInPrologueNotAllowed() {
        String code = "class Example {\n" +
                "    void helper() { }\n" +
                "    Example() {\n" +
                "        this.helper();\n" +
                "        super();\n" +
                "    }\n" +
                "}";
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(code));
        assertProblems(result, "(line 4,col 9) Statements before super() or this() cannot reference the current instance ('this').");
    }

    @Test
    void multipleExplicitConstructorCalls() {
        String code = "class Example {\n" +
                "    Example() { }\n" +
                "    Example(int x) {\n" +
                "        super();\n" +
                "        this();\n" +
                "    }\n" +
                "}";
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(code));
        assertProblems(result, "(line 5,col 9) Only one super() or this() call is allowed per constructor.");
    }

    @Test
    void thisInFieldInitializerBeforeSuper() {
        String code = "class Example {\n" +
                "    private int value;\n" +
                "    private int getValue() { return 42; }\n" +
                "    Example() {\n" +
                "        value = this.getValue();\n" +
                "        super();\n" +
                "    }\n" +
                "}";
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(code));
        assertProblems(result, "(line 5,col 9) Statements before super() or this() cannot reference the current instance ('this').");
    }
}
