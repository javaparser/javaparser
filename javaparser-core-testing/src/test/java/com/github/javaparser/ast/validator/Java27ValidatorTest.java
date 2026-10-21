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

import static com.github.javaparser.ParseStart.*;
import static com.github.javaparser.ParserConfiguration.LanguageLevel.JAVA_27;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.utils.TestUtils.assertNoProblems;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.stmt.Statement;
import org.junit.jupiter.api.Test;

/**
 * Test for Java 27 language level support.
 * Java 27 has no non-preview syntax changes, so features from earlier levels must keep working.
 */
class Java27ValidatorTest {

    private final JavaParser javaParser = new JavaParser(new ParserConfiguration().setLanguageLevel(JAVA_27));

    @Test
    void currentAndBleedingEdgeAreJava27() {
        assertEquals(JAVA_27, ParserConfiguration.LanguageLevel.CURRENT);
        assertEquals(JAVA_27, ParserConfiguration.LanguageLevel.BLEEDING_EDGE);
    }

    @Test
    void yieldSupported() {
        assertTrue(JAVA_27.isYieldSupported());
        ParseResult<Statement> result = javaParser.parse(
                STATEMENT, provider("int result = switch(x) { case 1 -> 10; default -> { yield 0; } };"));
        assertNoProblems(result);
    }

    @Test
    void moduleImportAllowed() {
        ParseResult<ImportDeclaration> result =
                javaParser.parse(IMPORT_DECLARATION, provider("import module java.base;"));
        assertNoProblems(result);
    }

    @Test
    void explicitConstructorInvocationAfterFirstStatementAllowed() {
        String code = "class Foo {\n" + "    public Foo() {\n"
                + "        int x = 2;\n"
                + "        super();\n"
                + "    }\n"
                + "}";

        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(code));
        assertNoProblems(result);
    }
}
