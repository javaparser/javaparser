/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2024 The JavaParser Team.
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

import static org.junit.jupiter.api.Assertions.*;

import com.github.javaparser.ParseProblemException;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.printer.ConfigurablePrinter;
import com.github.javaparser.printer.DefaultPrettyPrinter;
import com.github.javaparser.printer.configuration.DefaultConfigurationOption;
import com.github.javaparser.printer.configuration.DefaultPrinterConfiguration.ConfigOption;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.MockedStatic;
import org.mockito.Mockito;

class SourceRootTest {
    private final Path root = CodeGenerationUtils.mavenModuleRoot(SourceRootTest.class)
            .resolve("src/test/resources/com/github/javaparser/utils/");
    private final SourceRoot sourceRoot = new SourceRoot(root);
    private ConfigurablePrinter printer;

    @BeforeEach
    void before() {
        sourceRoot.getParserConfiguration().setLanguageLevel(ParserConfiguration.LanguageLevel.BLEEDING_EDGE);
        printer = new DefaultPrettyPrinter();
        sourceRoot.setPrinter(printer::print);
    }

    @Test
    void parseTestDirectory() throws IOException {
        List<ParseResult<CompilationUnit>> parseResults = sourceRoot.tryToParse();
        List<CompilationUnit> units = sourceRoot.getCompilationUnits();

        assertEquals(7, units.size());
        assertTrue(units.stream()
                .allMatch(unit -> !unit.getTypes().isEmpty() || unit.getModule().isPresent()));
        assertTrue(parseResults.stream().noneMatch(cu -> cu.getResult()
                .get()
                .getStorage()
                .get()
                .getPath()
                .toString()
                .contains("source.root")));
    }

    @Test
    void saveInCallback() throws IOException {
        printer.getConfiguration()
                .addOption(new DefaultConfigurationOption(
                        ConfigOption.END_OF_LINE_CHARACTER, LineSeparator.LF.asRawString()));
        sourceRoot.parse(
                "",
                sourceRoot.getParserConfiguration(),
                (localPath, absolutePath, result) -> SourceRoot.Callback.Result.SAVE);
    }

    @Test
    void saveInCallbackParallelized() {
        printer.getConfiguration()
                .addOption(new DefaultConfigurationOption(
                        ConfigOption.END_OF_LINE_CHARACTER, LineSeparator.LF.asRawString()));
        sourceRoot.parseParallelized(
                "",
                sourceRoot.getParserConfiguration(),
                ((localPath, absolutePath, result) -> SourceRoot.Callback.Result.SAVE));
    }

    @Test
    void fileAsRootIsNotAllowed() {
        assertThrows(IllegalArgumentException.class, () -> {
            Path path = CodeGenerationUtils.classLoaderRoot(SourceRootTest.class)
                    .resolve("com/github/javaparser/utils/Bla.java");
            new SourceRoot(path);
        });
    }

    @Test
    void dotsInRootDirectoryAreAllowed() throws IOException {
        Path path = CodeGenerationUtils.mavenModuleRoot(SourceRootTest.class)
                .resolve("src/test/resources/com/github/javaparser/utils/source.root");
        new SourceRoot(path).tryToParse();
    }

    @Test
    void dotsInPackageAreNotAllowed() {
        assertThrows(ParseProblemException.class, () -> {
            Path path = CodeGenerationUtils.mavenModuleRoot(SourceRootTest.class)
                    .resolve("src/test/resources/com/github/javaparser/utils");
            new SourceRoot(path).parse("source.root", "Y.java");
        });
    }

    @Test
    void isSensibleDirectoryToEnter() throws IOException {
        try (MockedStatic<Files> mockedFiles = Mockito.mockStatic(Files.class)) {
            mockedFiles.when(() -> Files.isHidden(Mockito.any())).thenReturn(false);
            mockedFiles.when(() -> Files.isDirectory(Mockito.any())).thenReturn(true);
            SourceRoot root = new SourceRoot(Paths.get("tests/01"));
            assertTrue(root.isSensibleDirectoryToEnter(root.getRoot()));
        }
    }

    private static Path normalizePath(Path p) {
        return p.toAbsolutePath().normalize();
    }

    @Test
    void resolvePath_resolves_relative_under_newRoot() {
        Path newRoot = Paths.get("new-root");
        SourceRoot sr = new SourceRoot(root);

        Path relKey = Paths.get("pkg/A.java");
        Path got = sr.resolvePath(newRoot, relKey);

        assertEquals(normalizePath(newRoot.resolve(relKey)), normalizePath(got));
    }

    @Test
    void resolvePath_returns_absolute_unchanged() {
        Path newRoot = Paths.get("new-root");
        SourceRoot sr = new SourceRoot(root);

        Path absKey = root.toAbsolutePath().resolve("pkg/B.java");
        Path got = sr.resolvePath(newRoot, absKey);

        assertEquals(normalizePath(absKey), normalizePath(got));
    }

    @Test
    void saveAll_uses_resolution_for_relative_and_absolute_keys() throws Exception {
        Path oldRoot = Files.createTempDirectory("jp-old-");
        Path newRoot = Files.createTempDirectory("jp-new-");
        SourceRoot sr = new SourceRoot(oldRoot);

        CompilationUnit cuRel = new CompilationUnit();
        sr.add("pkg", "Rel.java", cuRel);
        Path expectedRelTarget = normalizePath(newRoot.resolve("pkg/Rel.java"));
        assertEquals(expectedRelTarget,
                normalizePath(sr.resolvePath(newRoot, Paths.get("pkg/Rel.java"))));

        Path absKey = oldRoot.resolve("pkg/Abs.java").toAbsolutePath();
        Files.createDirectories(absKey.getParent());
        CompilationUnit cuAbs = new CompilationUnit();
        cuAbs.setStorage(absKey, java.nio.charset.StandardCharsets.UTF_8);
        sr.add(cuAbs);
        Path expectedAbsTarget = normalizePath(absKey);
        assertEquals(expectedAbsTarget, normalizePath(sr.resolvePath(newRoot, absKey)));
    }
}
