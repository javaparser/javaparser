/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2016 The JavaParser Team.
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

package com.github.javaparser.ast;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.Problem;
import org.junit.Test;

import static com.github.javaparser.ParseStart.COMPILATION_UNIT;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.utils.Utils.EOL;
import static org.assertj.core.api.Assertions.assertThat;

public class ParseResultTest {
    private final JavaParser javaParser = new JavaParser(new ParserConfiguration());

    @Test
    public void whenParsingSucceedsThenWeGetResultsAndNoProblems() {
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider("class X{}"));

        assertThat(result.getResult().isPresent()).isTrue();
        assertThat(result.getProblems()).isEmpty();
        assertThat(result.getTokens().isPresent()).isTrue();

        assertThat(result.toString()).isEqualTo("Parsing successful");
    }

    @Test
    public void whenParsingFailsThenWeGetProblemsAndNoResults() {
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider("class {"));

        assertThat(result.getResult().isPresent()).isFalse();
        assertThat(result.getProblems().size()).isEqualTo(1);

        Problem problem = result.getProblem(0);
        assertThat(problem.getMessage()).isEqualTo("Parse error");
        assertThat(result.getTokens().isPresent()).isTrue();

        assertThat(result.toString()).startsWith("Parsing failed:" + EOL +
                "Parse error at (line 1,col 1)" + EOL +
                "Problem stacktrace :");
    }
}
