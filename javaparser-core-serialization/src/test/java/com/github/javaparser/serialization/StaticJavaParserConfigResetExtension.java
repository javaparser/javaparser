/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2026 The JavaParser Team.
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

package com.github.javaparser.serialization;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import org.junit.jupiter.api.extension.AfterEachCallback;
import org.junit.jupiter.api.extension.BeforeEachCallback;
import org.junit.jupiter.api.extension.ExtensionContext;

/**
 * Resets StaticJavaParser to a blank ParserConfiguration before and after each
 * test, so tests don't leak parser state (language level, symbol resolver, etc.)
 * into each other.
 *
 * NOTE: incompatible with configuring StaticJavaParser in @BeforeAll if the test
 * class parses inside individual test methods rather than during @BeforeAll
 * itself — the resolver/config set up once will be wiped before each test runs.
 */
public class StaticJavaParserConfigResetExtension implements BeforeEachCallback, AfterEachCallback {

    @Override
    public void beforeEach(ExtensionContext context) {
        StaticJavaParser.setConfiguration(new ParserConfiguration());
    }

    @Override
    public void afterEach(ExtensionContext context) {
        StaticJavaParser.setConfiguration(new ParserConfiguration());
    }
}
