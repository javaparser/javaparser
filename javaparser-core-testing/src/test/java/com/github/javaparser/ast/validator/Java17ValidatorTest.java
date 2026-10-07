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
import static com.github.javaparser.ParserConfiguration.LanguageLevel.JAVA_17;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.utils.TestUtils.assertProblems;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.utils.TestUtils;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

class Java17ValidatorTest {

    private final JavaParser javaParser = new JavaParser(new ParserConfiguration().setLanguageLevel(JAVA_17));

    @Nested
    class Sealed {

        @Test
        void sealedAllowed() {
            ParseResult<CompilationUnit> result =
                    javaParser.parse(COMPILATION_UNIT, provider("sealed class X permits Y, Z {}"));
            TestUtils.assertNoProblems(result);
        }

        @Test
        void nonSealedAllowed() {
            ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider("non-sealed class X {}"));
            TestUtils.assertNoProblems(result);
        }

        @Test
        void sealedAndNonSealedRejectedOnLocalEnum() {
            ParseResult<CompilationUnit> result =
                    javaParser.parse(COMPILATION_UNIT, provider("class X{ void x() {sealed non-sealed enum E{A,B}}}"));
            assertProblems(
                    result,
                    "(line 1,col 20) 'sealed' is not allowed here.",
                    "(line 1,col 20) 'non-sealed' is not allowed here.");
        }

        @Test
        void strictfpAllowedOnLocalEnum() {
            ParseResult<CompilationUnit> result =
                    javaParser.parse(COMPILATION_UNIT, provider("class X{ void x() {strictfp enum E{A,B}}}"));
            TestUtils.assertNoProblems(result);
        }
    }
}
