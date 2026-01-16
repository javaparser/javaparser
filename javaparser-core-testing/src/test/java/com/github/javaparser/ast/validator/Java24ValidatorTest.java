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

package com.github.javaparser.ast.validator;

import static com.github.javaparser.ParseStart.COMPILATION_UNIT;
import static com.github.javaparser.ParseStart.STATEMENT;
import static com.github.javaparser.ParserConfiguration.LanguageLevel.JAVA_24;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.utils.TestUtils.assertNoProblems;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.stmt.Statement;
import org.junit.jupiter.api.Test;

/**
 * Test for Java 24 language level support.
 * Tests basic functionality inherited from Java 23.
 *
 * @see <a href="https://openjdk.org/projects/jdk/24/">https://openjdk.org/projects/jdk/24/</a>
 */
class Java24ValidatorTest {

    private final JavaParser javaParser = new JavaParser(new ParserConfiguration().setLanguageLevel(JAVA_24));

    @Test
    void basicParsing() {
        ParseResult<CompilationUnit> result =
                javaParser.parse(COMPILATION_UNIT, provider("class X { void m() { System.out.println(\"Hello\"); } }"));
        assertNoProblems(result);
    }

    @Test
    void yieldStatementSupported() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("yield 42;"));
        assertNoProblems(result);
    }

    @Test
    void switchExpressionSupported() {
        ParseResult<Statement> result = javaParser.parse(
                STATEMENT, provider("int result = switch(x) { case 1 -> 10; case 2 -> 20; default -> 0; };"));
        assertNoProblems(result);
    }

    @Test
    void recordsSupported() {
        ParseResult<CompilationUnit> result =
                javaParser.parse(COMPILATION_UNIT, provider("record Point(int x, int y) {}"));
        assertNoProblems(result);
    }

    @Test
    void textBlocksSupported() {
        ParseResult<CompilationUnit> result = javaParser.parse(
                COMPILATION_UNIT, provider("class X { String s = \"\"\"\n    Hello\n    World\n    \"\"\"; }"));
        assertNoProblems(result);
    }

    @Test
    void unnamedVariablesFromJava22Supported() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("int _ = 42;"));
        assertNoProblems(result);
    }
}
