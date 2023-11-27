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
import com.github.javaparser.utils.TestUtils;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.ParseStart.COMPILATION_UNIT;
import static com.github.javaparser.ParseStart.STATEMENT;
import static com.github.javaparser.ParserConfiguration.LanguageLevel.JAVA_16;
import static com.github.javaparser.Providers.provider;

class Java16ValidatorTest {

    private final JavaParser javaParser = new JavaParser(new ParserConfiguration().setLanguageLevel(JAVA_16));

    @Nested
    class Yield {
        @Test
        void yieldAllowed() {
            ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("switch(x){case 3: yield 6;}"));
            TestUtils.assertNoProblems(result);
        }

    }

    /**
     * Records are available within Java 14 (preview), Java 15 (2nd preview), and Java 16 (release).
     * The introduction of records means that they are no longer able to be used as identifiers.
     */
    @Nested
    class Record {

        @Nested
        class RecordAsTypeIdentifierForbidden {
            @Test
            void recordUsedAsClassIdentifier() {
                String s = "public class record {}";
                ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(s));
                TestUtils.assertProblems(result, "(line 1,col 14) 'record' is a restricted identifier and cannot be used for type declarations");
            }

            @Test
            void recordUsedAsEnumIdentifier() {
                String s = "public enum record {}";
                ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(s));
                TestUtils.assertProblems(result, "(line 1,col 13) 'record' is a restricted identifier and cannot be used for type declarations");
            }

            @Test
            void recordUsedAsRecordIdentifier() {
                String s = "public record record() {}";
                ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(s));
                TestUtils.assertProblems(result, "(line 1,col 15) 'record' is a restricted identifier and cannot be used for type declarations");
            }
        }

        @Nested
        class RecordUsedAsIdentifierAllowedAsFieldDeclarations {
            @Test
            void recordUsedAsFieldIdentifierInClass() {
                String s = "class X { int record; }";
                ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(s));
                TestUtils.assertNoProblems(result);
            }

            @Test
            void recordUsedAsFieldIdentifierInInterface() {
                String s = "interface X { int record; }";
                ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(s));
                TestUtils.assertNoProblems(result);
            }
        }

        @Nested
        class RecordDeclarationPermitted {
            @Test
            void recordDeclaration() {
                String s = "record X() { }";
                ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(s));
                TestUtils.assertNoProblems(result);
            }
        }
    }
}
