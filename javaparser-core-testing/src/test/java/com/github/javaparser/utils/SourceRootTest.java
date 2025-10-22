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
import com.github.javaparser.Problem;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.printer.ConfigurablePrinter;
import com.github.javaparser.printer.DefaultPrettyPrinter;
import com.github.javaparser.printer.configuration.DefaultConfigurationOption;
import com.github.javaparser.printer.configuration.DefaultPrinterConfiguration.ConfigOption;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Collections;
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

    @Test
    void getSourcePathTest() throws IOException {
        Path path = CodeGenerationUtils.mavenModuleRoot(SourceRootTest.class)
                .resolve("src/test/resources/com/github/javaparser/utils/.abc");
        SourceRoot sr = new SourceRoot(path);
        List<ParseResult<CompilationUnit>> results = sr.tryToParse("");
        Path filePath = path.resolve("bla.java");
        // Assert for getSourcePath:
        assertEquals(1, results.size());
        ParseResult<CompilationUnit> r = results.get(0);
        assertTrue(r.getSourcePath().isPresent(), "Expected source path to be present");
        assertEquals(filePath.toAbsolutePath(), r.getSourcePath().get());
    }

    @Test
    void sourcePathToStringTest() {
        Problem problem = new Problem("problem", null, null);
        // sourcePath not set -> no " for <path>" in message
        ParseResult<CompilationUnit> r = new ParseResult<>(null, Collections.singletonList(problem), null);
        assertFalse(r.getSourcePath().isPresent());
        String s = r.toString();
        assertFalse(s.contains(" for "));
        // sourcePath set -> message contains " for <path>"
        Path p = Paths.get("SomeFile.java").toAbsolutePath();
        ParseResult<CompilationUnit> r2 = new ParseResult<>(null, Collections.singletonList(problem), null);
        r2.setSourcePath(p);
        assertTrue(r2.getSourcePath().isPresent());
        assertTrue(r2.toString().startsWith("Parsing failed for " + p));
    }

    @Test
    void resolvePathRelativeToNewRoot() {
        SourceRoot sr = new SourceRoot(CodeGenerationUtils.mavenModuleRoot(SourceRootTest.class));
        Path newRoot = Paths.get("root");
        Path relative = Paths.get("pkg/../pkg/A.java");
        Path got = sr.resolvePath(newRoot, relative);
        assertEquals(newRoot.resolve("pkg/A.java").normalize(), got);
    }

    @Test
    void resolvePathKeepsAbsolutePath() {
        SourceRoot sr = new SourceRoot(CodeGenerationUtils.mavenModuleRoot(SourceRootTest.class));

        Path abs = Paths.get("absdir/../absdir/B.java").toAbsolutePath();
        Path newRoot = Paths.get("anotherRoot");
        Path got = sr.resolvePath(newRoot, abs);
        assertEquals(abs.normalize(), got, "absolute path must not be re-rooted");
    }

    @Test
    void resolvePathNullArgsThrowException() {
        SourceRoot sr = new SourceRoot(CodeGenerationUtils.mavenModuleRoot(SourceRootTest.class));
        Path p = Paths.get("pkg/C.java");
        assertThrows(NullPointerException.class, () -> sr.resolvePath(null, p));
        assertThrows(NullPointerException.class, () -> sr.resolvePath(Paths.get("root"), null));
    }

    @Test
    void saveAllPreservesAbsolutePaths() throws Exception {
        Path tmp = Files.createTempDirectory("jp-core-");
        Path oldRoot = tmp.resolve("old");
        Path newRoot = tmp.resolve("new");

        Files.createDirectories(oldRoot);

        SourceRoot sr = new SourceRoot(oldRoot);
        CompilationUnit cuRel = new CompilationUnit();
        cuRel.setPackageDeclaration("p");
        ClassOrInterfaceDeclaration rDecl = new ClassOrInterfaceDeclaration();
        rDecl.setName("R");
        rDecl.setInterface(false);
        cuRel.addType(rDecl);
        sr.add("p", "R.java", cuRel);

        Path expectedRelativeTarget =
                newRoot.resolve("p/R.java").toAbsolutePath().normalize();
        assertFalse(Files.exists(expectedRelativeTarget.getParent()), "parent dir should not exist before save");

        Path absDir = tmp.resolve("abs");
        Path absPath = absDir.resolve("X.java").toAbsolutePath();
        CompilationUnit cuAbs = new CompilationUnit();
        cuAbs.setPackageDeclaration("abs");
        ClassOrInterfaceDeclaration xDecl = new ClassOrInterfaceDeclaration();
        xDecl.setName("X");
        xDecl.setInterface(false);
        cuAbs.addType(xDecl);
        cuAbs.setStorage(absPath, StandardCharsets.UTF_8);
        sr.add(cuAbs);

        sr.saveAll(newRoot, StandardCharsets.UTF_8);

        assertTrue(Files.isDirectory(expectedRelativeTarget.getParent()), "parent directory should be created");
        assertTrue(Files.isRegularFile(expectedRelativeTarget), "relative CU should be saved under newRoot");

        assertTrue(Files.isRegularFile(absPath), "absolute-storage CU should be saved at its absolute path");

        assertTrue(Files.size(expectedRelativeTarget) > 0);
        assertTrue(Files.size(absPath) > 0);
    }
}
