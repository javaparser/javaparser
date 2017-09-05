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

package com.github.javaparser.utils;

import com.github.javaparser.ParseResult;
import com.github.javaparser.ast.CompilationUnit;
import org.junit.Test;

import java.io.IOException;
import java.net.URISyntaxException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class SourceZipTest {

    private final Path testDir = CodeGenerationUtils.mavenModuleRoot(SourceZipTest.class)
            .resolve(Paths.get("..", "javaparser-testing", "src", "test", "resources", "com", "github", "javaparser",
                    "source_zip"))
            .normalize();

    @Test
    public void parseTestDirectory() throws URISyntaxException, IOException {
        SourceZip sourceZip = new SourceZip(testDir.resolve("test.zip"));
        List<Pair<Path, ParseResult<CompilationUnit>>> results = sourceZip.parse();
        assertEquals(3, results.size());
        List<CompilationUnit> units = new ArrayList<>();
        for (Pair<Path, ParseResult<CompilationUnit>> pr : results) {
            units.add(pr.b.getResult().get());
        }
        assertTrue(units.stream().noneMatch(unit -> unit.getTypes().isEmpty()));
    }

    @Test
    public void parseTestDirectoryWithCallback() throws URISyntaxException, IOException {
        SourceZip sourceZip = new SourceZip(testDir.resolve("test.zip"));
        List<Pair<Path, ParseResult<CompilationUnit>>> results = new ArrayList<>();

        sourceZip.parse((path, result) -> results.add(new Pair<>(path, result)));

        assertEquals(3, results.size());
        List<CompilationUnit> units = new ArrayList<>();
        for (Pair<Path, ParseResult<CompilationUnit>> pr : results) {
            units.add(pr.b.getResult().get());
        }
        assertTrue(units.stream().noneMatch(unit -> unit.getTypes().isEmpty()));
    }

    @Test(expected = IOException.class)
    public void dirAsZipIsNotAllowed() throws IOException {
        new SourceZip(testDir.resolve("test")).parse();
    }

    @Test(expected = IOException.class)
    public void fileAsZipIsNotAllowed() throws IOException {
        new SourceZip(testDir.resolve("test.txt")).parse();
    }
}
