/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2025 The JavaParser Team.
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
import static com.github.javaparser.ParserConfiguration.LanguageLevel.*;
import static com.github.javaparser.Providers.provider;
import static org.junit.jupiter.api.Assertions.*;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import org.junit.jupiter.api.Test;

/**
 * Tests for the LanguageLevel enum and related functionality.
 * Verifies that new Java versions (23, 24, 25) are properly supported.
 */
class LanguageLevelTest {

    @Test
    void java23EnumExists() {
        assertNotNull(JAVA_23);
        assertEquals("JAVA_23", JAVA_23.name());
    }

    @Test
    void java24EnumExists() {
        assertNotNull(JAVA_24);
        assertEquals("JAVA_24", JAVA_24.name());
    }

    @Test
    void java25EnumExists() {
        assertNotNull(JAVA_25);
        assertEquals("JAVA_25", JAVA_25.name());
    }

    @Test
    void bleedingEdgeIsJava25() {
        assertEquals(JAVA_25, BLEEDING_EDGE);
    }

    @Test
    void java23SupportsYield() {
        assertTrue(JAVA_23.isYieldSupported());
    }

    @Test
    void java24SupportsYield() {
        assertTrue(JAVA_24.isYieldSupported());
    }

    @Test
    void java25SupportsYield() {
        assertTrue(JAVA_25.isYieldSupported());
    }

    @Test
    void canConfigureParserWithJava23() {
        JavaParser parser = new JavaParser(new ParserConfiguration().setLanguageLevel(JAVA_23));
        ParseResult<CompilationUnit> result = parser.parse(COMPILATION_UNIT, provider("class Test {}"));
        assertTrue(result.isSuccessful());
    }

    @Test
    void canConfigureParserWithJava24() {
        JavaParser parser = new JavaParser(new ParserConfiguration().setLanguageLevel(JAVA_24));
        ParseResult<CompilationUnit> result = parser.parse(COMPILATION_UNIT, provider("class Test {}"));
        assertTrue(result.isSuccessful());
    }

    @Test
    void canConfigureParserWithJava25() {
        JavaParser parser = new JavaParser(new ParserConfiguration().setLanguageLevel(JAVA_25));
        ParseResult<CompilationUnit> result = parser.parse(COMPILATION_UNIT, provider("class Test {}"));
        assertTrue(result.isSuccessful());
    }

    @Test
    void java23ValidatorIsNotNull() {
        assertNotNull(JAVA_23.validator);
    }

    @Test
    void java24ValidatorIsNotNull() {
        assertNotNull(JAVA_24.validator);
    }

    @Test
    void java25ValidatorIsNotNull() {
        assertNotNull(JAVA_25.validator);
    }

    @Test
    void java23PostProcessorIsNotNull() {
        assertNotNull(JAVA_23.postProcessor);
    }

    @Test
    void java24PostProcessorIsNotNull() {
        assertNotNull(JAVA_24.postProcessor);
    }

    @Test
    void java25PostProcessorIsNotNull() {
        assertNotNull(JAVA_25.postProcessor);
    }
}
