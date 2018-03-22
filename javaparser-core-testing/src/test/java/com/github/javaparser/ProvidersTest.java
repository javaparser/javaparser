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

package com.github.javaparser;

import com.github.javaparser.ast.CompilationUnit;
import org.junit.Test;

import java.io.IOException;
import java.nio.charset.Charset;

import static org.junit.Assert.*;

public class ProvidersTest {

    @Test
    public void testResourceProvider() throws IOException {
        Provider provider = Providers.resourceProvider("com/github/javaparser/issue_samples/Issue290.java.txt");
        assertNotNull(provider);
        JavaParser parser = new JavaParser();
        ParseResult<CompilationUnit> parse = parser.parse(ParseStart.COMPILATION_UNIT, provider);
        assertTrue(parse.isSuccessful());
    }

    @Test
    public void testResourceProviderWithWrongEncoding() throws IOException {
        Provider provider = Providers.resourceProvider("com/github/javaparser/TestFileIso88591.java");
        assertNotNull(provider);
        JavaParser parser = new JavaParser();
        ParseResult<CompilationUnit> parse = parser.parse(ParseStart.COMPILATION_UNIT, provider);
        assertFalse(parse.isSuccessful());
    }

    @Test
    public void testResourceProviderWithEncoding() throws IOException {
        Provider provider = Providers.resourceProvider(
                "com/github/javaparser/TestFileIso88591.java",
                Charset.forName("ISO-8859-1")
        );
        assertNotNull(provider);
        JavaParser parser = new JavaParser();
        ParseResult<CompilationUnit> parse = parser.parse(ParseStart.COMPILATION_UNIT, provider);
        assertTrue(parse.isSuccessful());
    }
}
