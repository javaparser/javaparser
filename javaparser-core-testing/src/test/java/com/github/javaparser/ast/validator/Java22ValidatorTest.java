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

import static com.github.javaparser.ParseStart.EXPRESSION;
import static com.github.javaparser.ParseStart.STATEMENT;
import static com.github.javaparser.ParserConfiguration.LanguageLevel.JAVA_22;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.utils.TestUtils.assertNoProblems;
import static com.github.javaparser.utils.TestUtils.assertProblems;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.stmt.Statement;
import org.junit.jupiter.api.Test;

/**
 * See <a href="https://openjdk.org/jeps/456">JEP456</a> for descriptions of the cases tested here.
 */
class Java22ValidatorTest {

    private final JavaParser javaParser = new JavaParser(new ParserConfiguration().setLanguageLevel(JAVA_22));

    @Test
    void matchAllAllowedInRecordList() {
        ParseResult<Expression> result =
                javaParser.parse(EXPRESSION, provider("switch(x){case Box(_) -> System.out.println(0);}"));
        assertNoProblems(result);
    }

    @Test
    void matchAllNotAllowedAsTopLevelPattern() {
        ParseResult<Expression> result =
                javaParser.parse(EXPRESSION, provider("switch(x){case _ -> System.out.println(0);}"));
        assertProblems(result, "(line 1,col 16) Unnamed variables only supported in cases described by JEP456");
    }

    @Test
    void unnamedTypePatternAllowed() {
        ParseResult<Expression> result =
                javaParser.parse(EXPRESSION, provider("switch(x){case Foo _ -> System.out.println(0);}"));
        assertNoProblems(result);
    }

    @Test
    void unnamedVariableDeclaratorAllowed() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("int _ = 42;"));
        assertNoProblems(result);
    }

    @Test
    void unnamedVariableAllowedInForEach() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("for (Foo _ : items) {}"));
        assertNoProblems(result);
    }

    @Test
    void unnamedVariableAllowedInForUpdate() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("for (int i = 0; _ = foo(); i++) {}"));
        assertNoProblems(result);
    }

    @Test
    void unnamedVariableAllowedInCatchBlock() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("try {} catch (Exception _) {}"));
        assertNoProblems(result);
    }

    @Test
    void unnamedVariableAllowedInTryWithResources() {
        ParseResult<Statement> result =
                javaParser.parse(STATEMENT, provider("try(var _ = foo()) {} catch (Exception e) {}"));
        assertNoProblems(result);
    }

    @Test
    void unnamedVariableAllowedAsLambdaParameter() {
        ParseResult<Expression> result = javaParser.parse(EXPRESSION, provider("foo(_ -> System.out.println(0))"));
        assertNoProblems(result);
    }

    @Test
    void unnamedVariableNotAllowedAsArgument() {
        ParseResult<Expression> result = javaParser.parse(EXPRESSION, provider("foo(_)"));
        assertProblems(result, "(line 1,col 5) Unnamed variables only supported in cases described by JEP456");
    }

    @Test
    void unnamedVariableNotAllowedInNonDeclAssignment() {
        ParseResult<Expression> result = javaParser.parse(EXPRESSION, provider("_ = 12"));
        assertProblems(result, "(line 1,col 1) Unnamed variables only supported in cases described by JEP456");
    }

    @Test
    void unnamedVariableNotAllowedInForUpdate() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("for (;; _++) {}"));
        assertProblems(result, "(line 1,col 9) Unnamed variables only supported in cases described by JEP456");
    }

    @Test
    void unnamedVariableNotAllowedOnRhsInForCondition() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("for (; x = _; ) {}"));
        assertProblems(result, "(line 1,col 12) Unnamed variables only supported in cases described by JEP456");
    }
}
