/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.stmt.Statement;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.ParseStart.COMPILATION_UNIT;
import static com.github.javaparser.ParseStart.STATEMENT;
import static com.github.javaparser.ParserConfiguration.LanguageLevel.JAVA_8;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.ast.validator.Java1_1ValidatorTest.allModifiers;
import static com.github.javaparser.utils.TestUtils.assertNoProblems;
import static com.github.javaparser.utils.TestUtils.assertProblems;

class Java8ValidatorTest {
    public static final JavaParser javaParser = new JavaParser(new ParserConfiguration().setLanguageLevel(JAVA_8));

    @Test
    void localInterface() {
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider("class X {void a(){interface I{}};}"));
        assertProblems(result, "(line 1,col 19) There is no such thing as a local interface.");
    }

    @Test
    void lambdaParameter() {
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider("class X{int x(){ a((" + allModifiers + " Integer x) -> 10);}}"));
        assertProblems(result,
                "(line 1,col 21) Can have only one of 'public', 'protected', 'private'.",
                "(line 1,col 21) Can have only one of 'final', 'abstract'.",
                "(line 1,col 21) Can have only one of 'native', 'strictfp'.",
                "(line 1,col 21) 'transient' is not allowed here.",
                "(line 1,col 21) 'volatile' is not allowed here.",
                "(line 1,col 21) 'synchronized' is not allowed here.",
                "(line 1,col 21) 'strictfp' is not allowed here.",
                "(line 1,col 21) 'default' is not allowed here.",
                "(line 1,col 21) 'native' is not allowed here.",
                "(line 1,col 21) 'strictfp' is not allowed here.",
                "(line 1,col 21) 'abstract' is not allowed here.",
                "(line 1,col 21) 'static' is not allowed here.",
                "(line 1,col 21) 'transitive' is not allowed here.",
                "(line 1,col 21) 'private' is not allowed here.",
                "(line 1,col 21) 'public' is not allowed here.",
                "(line 1,col 21) 'protected' is not allowed here."
        );
    }

    @Test
    void interfaceMethod() {
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider("interface X{" + allModifiers + "int x(){};}"));
        assertProblems(result,
                "(line 1,col 13) Can have only one of 'public', 'protected', 'private'.",
                "(line 1,col 13) Can have only one of 'final', 'abstract'.",
                "(line 1,col 13) Can have only one of 'native', 'strictfp'.",
                "(line 1,col 13) Cannot be 'abstract' and also 'private', 'static', 'final', 'native', 'strictfp', 'synchronized'.",
                "(line 1,col 13) 'transient' is not allowed here.",
                "(line 1,col 13) 'volatile' is not allowed here.",
                "(line 1,col 13) 'transitive' is not allowed here.",
                "(line 1,col 13) 'private' is not allowed here."
        );
    }

    @Test
    void defaultMethodWithoutBody() {
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider("interface X {default void a();}"));
        assertProblems(result, "(line 1,col 14) 'default' methods must have a body.");
    }

    @Test
    void lambdas() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("a(() -> 1);"));
        assertNoProblems(result);
    }

    @Test
    void noModules() {
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider("open module x {}"));
        assertProblems(result, "(line 1,col 1) Modules are not supported.");
    }
}
