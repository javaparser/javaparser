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

package com.github.javaparser.utils;

import static com.github.javaparser.ParserConfiguration.LanguageLevel.JAVA_16;
import static com.github.javaparser.ParserConfiguration.LanguageLevel.JAVA_7;
import static com.github.javaparser.ParserConfiguration.LanguageLevel.JAVA_8;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.Problem;
import java.util.List;
import org.junit.jupiter.api.Test;
import org.opentest4j.AssertionFailedError;

class TestParserTest {

    @Test
    void parseProblemsRemainAssertionFailuresWithTheCompleteProblemList() {
        String source = "class A { Runnable first = () -> {}; Runnable second = () -> {}; }";
        JavaParser parser = new JavaParser(new ParserConfiguration().setLanguageLevel(JAVA_7));
        List<Problem> problems = parser.parse(source).getProblems();
        assertEquals(2, problems.size());

        AssertionFailedError failure = assertThrows(
                AssertionFailedError.class, () -> TestParser.parseCompilationUnit(JAVA_7, source));

        assertEquals(problems.toString(), failure.getMessage());
    }

    @Test
    void defaultAndExplicitLanguageLevelsRemainIndependent() {
        String source = "record Person(String name) {}";

        assertThrows(AssertionFailedError.class, () -> TestParser.parseCompilationUnit(JAVA_8, source));
        assertTrue(TestParser.parseCompilationUnit(source).getType(0).isRecordDeclaration());
        assertTrue(TestParser.parseCompilationUnit(JAVA_16, source)
                .getType(0)
                .isRecordDeclaration());
        assertThrows(AssertionFailedError.class, () -> TestParser.parseCompilationUnit(JAVA_8, source));
    }
}
