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
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.utils.TestUtils;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.ParseStart.EXPRESSION;
import static com.github.javaparser.ParseStart.STATEMENT;
import static com.github.javaparser.ParserConfiguration.LanguageLevel.JAVA_21;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.utils.TestUtils.assertNoProblems;

class Java21ValidatorTest {

    private final JavaParser javaParser = new JavaParser(new ParserConfiguration().setLanguageLevel(JAVA_21));

    @Test
    void switchDefaultCaseAllowed() {
        ParseResult<Expression> result = javaParser.parse(EXPRESSION, provider("switch(x){case null, default -> System.out.println(0);}"));
        assertNoProblems(result);
    }

    @Test
    void switchPatternWithGuardAllowed() {
        ParseResult<Expression> result = javaParser.parse(EXPRESSION, provider("switch(x){case String s when s.length() > 5 -> System.out.println(0);}"));
        assertNoProblems(result);
    }

    @Test
    void recordPatternsAllowed() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("if (a instanceof Box(String s)) {}"));
        TestUtils.assertNoProblems(result);
    }

}
