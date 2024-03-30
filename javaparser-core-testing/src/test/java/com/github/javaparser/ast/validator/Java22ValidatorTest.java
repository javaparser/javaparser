/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2024 The JavaParser Team.
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
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.utils.TestUtils;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.ParseStart.*;
import static com.github.javaparser.ParserConfiguration.LanguageLevel.JAVA_22_INCOMPLETE;
import static com.github.javaparser.Providers.provider;

class Java22ValidatorTest {

    private final JavaParser javaParser = new JavaParser(new ParserConfiguration().setLanguageLevel(JAVA_22_INCOMPLETE));

    /**
     * Unnamed Variables & Patterns available within Java 21 (preview), Java 22 (release).
     */
    @Nested
    class UnnamedVariables {
        @Test
        void variable() {
            ParseResult<VariableDeclarationExpr> result = javaParser.parse(VARIABLE_DECLARATION_EXPR, provider("Order _"));
            TestUtils.assertNoProblems(result);
        }

        @Test
        void forLoop() {
            ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("for (int i = 0, _ = sideEffect(); i < 10; i++) {}"));
            TestUtils.assertNoProblems(result);
        }

        @Test
        void varDeclaration() {
            ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("var _ = q.remove();"));
            TestUtils.assertNoProblems(result);
        }

        @Test
        void varTryCatch() {
            ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("try {} catch (NumberFormatException _) {}"));
            TestUtils.assertNoProblems(result);
        }

        @Test
        void varLambda() {
            ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("Collectors.toMap(String::toUpperCase, _ -> \"NODATA\");"));
            TestUtils.assertNoProblems(result);
        }

        @Test
        void varPatternMatching() {
            ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("switch (o) { case Integer _ -> {} }"));
            TestUtils.assertNoProblems(result);
        }

    }

    @Nested
    class UnnamedPatterns {

    }


}
