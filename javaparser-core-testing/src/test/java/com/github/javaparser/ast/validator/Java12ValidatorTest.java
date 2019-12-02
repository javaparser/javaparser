/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2019 The JavaParser Team.
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
import com.github.javaparser.ast.stmt.Statement;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.ParseStart.STATEMENT;
import static com.github.javaparser.ParserConfiguration.LanguageLevel.JAVA_12;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.utils.TestUtils.assertNoProblems;

class Java12ValidatorTest {
    public static final JavaParser javaParser = new JavaParser(new ParserConfiguration().setLanguageLevel(JAVA_12));

    @Test
    void expressionsInLabelsNotAllowed() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("switch(x){case 3+4+5: ;}"));
        assertNoProblems(result);
    }

    @Test
    void switchExpressionNotAllowed() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("int a = switch(x){};"));
        assertNoProblems(result);
    }

    @Test
    void multiLabelCaseAllowed() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("switch(x){case 3,4,5: ;}"));
        assertNoProblems(result);
    }
}
