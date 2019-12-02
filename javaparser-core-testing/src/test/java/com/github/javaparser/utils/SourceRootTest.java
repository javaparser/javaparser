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

package com.github.javaparser.utils;

import com.github.javaparser.ParseProblemException;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Path;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.assertThrows;

class SourceRootTest {
    private final Path root = CodeGenerationUtils.mavenModuleRoot(SourceRootTest.class).resolve("src/test/resources/com/github/javaparser/utils/");
    private final SourceRoot sourceRoot = new SourceRoot(root);

    @BeforeEach
    void before() {
        sourceRoot.getParserConfiguration().setLanguageLevel(ParserConfiguration.LanguageLevel.BLEEDING_EDGE);
    }

    @Test
    void parseTestDirectory() throws IOException {

        List<ParseResult<CompilationUnit>> parseResults = sourceRoot.tryToParse();
        List<CompilationUnit> units = sourceRoot.getCompilationUnits();

        assertEquals(2, units.size());
        assertTrue(units.stream().allMatch(unit -> !unit.getTypes().isEmpty() || unit.getModule().isPresent()));
        assertTrue(parseResults.stream().noneMatch(cu -> cu.getResult().get().getStorage().get().getPath().toString().contains("source.root")));
    }

    @Test
    void saveInCallback() throws IOException {
        sourceRoot.parse("", sourceRoot.getParserConfiguration(), (localPath, absolutePath, result) -> SourceRoot.Callback.Result.SAVE);
    }

    @Test
    void saveInCallbackParallelized() {
        sourceRoot.parseParallelized("", sourceRoot.getParserConfiguration(), ((localPath, absolutePath, result) ->
                SourceRoot.Callback.Result.SAVE));
    }

    @Test
    void fileAsRootIsNotAllowed() {
        assertThrows(IllegalArgumentException.class, () -> {
            Path path = CodeGenerationUtils.classLoaderRoot(SourceRootTest.class).resolve("com/github/javaparser/utils/Bla.java");
        new SourceRoot(path);
    });
}

    @Test
    void dotsInRootDirectoryAreAllowed() throws IOException {
        Path path = CodeGenerationUtils.mavenModuleRoot(SourceRootTest.class).resolve("src/test/resources/com/github/javaparser/utils/source.root");
        new SourceRoot(path).tryToParse();
    }

    @Test
    void dotsInPackageAreNotAllowed() {
        assertThrows(ParseProblemException.class, () -> {
            Path path = CodeGenerationUtils.mavenModuleRoot(SourceRootTest.class).resolve("src/test/resources/com/github/javaparser/utils");
        new SourceRoot(path).parse("source.root", "Y.java");
    });
}
}
