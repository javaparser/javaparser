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

package com.github.javaparser.generator.core.other;

import static com.github.javaparser.generator.GeneratorTestHelper.createTempSourceRoot;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.utils.SourceRoot;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Comprehensive tests for BndGenerator.
 * Verifies that bnd.bnd file is correctly generated with exported packages.
 */
class BndGeneratorTest {

    private SourceRoot sourceRoot;
    private BndGenerator generator;
    private Path tempProjectRoot;

    @BeforeEach
    void setUp(@TempDir Path tempDir) throws Exception {
        tempProjectRoot = tempDir;
        Path srcMainJava = tempProjectRoot.resolve("javaparser-core").resolve("src").resolve("main").resolve("java");
        Files.createDirectories(srcMainJava);
        sourceRoot = new SourceRoot(srcMainJava);
        generator = new BndGenerator(sourceRoot);
    }

    @Test
    void testGeneratorInitialization() {
        assertNotNull(generator);
        assertNotNull(generator.sourceRoot);
        assertEquals(sourceRoot, generator.sourceRoot);
    }

    @Test
    void testBndFileGeneration() throws IOException {
        // Create some test packages
        CompilationUnit cu1 = new CompilationUnit("com.github.javaparser.ast");
        sourceRoot.add(cu1);
        CompilationUnit cu2 = new CompilationUnit("com.github.javaparser.ast.expr");
        sourceRoot.add(cu2);

        // Create template file
        Path templateFile = tempProjectRoot.resolve("bnd.bnd.template");
        Files.write(templateFile, "Bundle-Name: JavaParser\n{exportedPackages}\n".getBytes());

        generator.generate();

        Path outputFile = tempProjectRoot.resolve("bnd.bnd");
        assertTrue(Files.exists(outputFile), "bnd.bnd file should be created");
    }

    @Test
    void testPackageListGeneration() throws IOException {
        CompilationUnit cu1 = new CompilationUnit("com.github.javaparser.ast");
        sourceRoot.add(cu1);
        CompilationUnit cu2 = new CompilationUnit("com.github.javaparser.ast.expr");
        sourceRoot.add(cu2);
        CompilationUnit cu3 = new CompilationUnit("com.github.javaparser.utils");
        sourceRoot.add(cu3);

        Path templateFile = tempProjectRoot.resolve("bnd.bnd.template");
        Files.write(templateFile, "{exportedPackages}".getBytes());

        generator.generate();

        Path outputFile = tempProjectRoot.resolve("bnd.bnd");
        String content = new String(Files.readAllBytes(outputFile));
        assertTrue(content.contains("com.github.javaparser.ast"), "Should contain package name");
        assertTrue(content.contains("com.github.javaparser.ast.expr"), "Should contain package name");
        assertTrue(content.contains("com.github.javaparser.utils"), "Should contain package name");
    }

    @Test
    void testPackagesAreSorted() throws IOException {
        CompilationUnit cu1 = new CompilationUnit("com.github.javaparser.z");
        sourceRoot.add(cu1);
        CompilationUnit cu2 = new CompilationUnit("com.github.javaparser.a");
        sourceRoot.add(cu2);
        CompilationUnit cu3 = new CompilationUnit("com.github.javaparser.m");
        sourceRoot.add(cu3);

        Path templateFile = tempProjectRoot.resolve("bnd.bnd.template");
        Files.write(templateFile, "{exportedPackages}".getBytes());

        generator.generate();

        Path outputFile = tempProjectRoot.resolve("bnd.bnd");
        String content = new String(Files.readAllBytes(outputFile));
        int indexA = content.indexOf("com.github.javaparser.a");
        int indexM = content.indexOf("com.github.javaparser.m");
        int indexZ = content.indexOf("com.github.javaparser.z");
        assertTrue(indexA < indexM && indexM < indexZ, "Packages should be sorted");
    }

    @Test
    void testTemplateReplacement() throws IOException {
        CompilationUnit cu = new CompilationUnit("com.github.javaparser.ast");
        sourceRoot.add(cu);

        Path templateFile = tempProjectRoot.resolve("bnd.bnd.template");
        Files.write(templateFile, "Bundle-Name: JavaParser\n{exportedPackages}\nBundle-Version: 1.0".getBytes());

        generator.generate();

        Path outputFile = tempProjectRoot.resolve("bnd.bnd");
        String content = new String(Files.readAllBytes(outputFile));
        assertTrue(content.contains("Bundle-Name: JavaParser"), "Should contain template content");
        assertTrue(content.contains("Bundle-Version: 1.0"), "Should contain template content");
        assertTrue(content.contains("com.github.javaparser.ast"), "Should contain package list");
    }

    @Test
    void testEmptySourceRoot() throws IOException {
        Path templateFile = tempProjectRoot.resolve("bnd.bnd.template");
        Files.write(templateFile, "{exportedPackages}".getBytes());

        generator.generate();

        Path outputFile = tempProjectRoot.resolve("bnd.bnd");
        assertTrue(Files.exists(outputFile), "bnd.bnd file should be created even with no packages");
    }

    @Test
    void testDuplicatePackagesAreRemoved() throws IOException {
        CompilationUnit cu1 = new CompilationUnit("com.github.javaparser.ast");
        sourceRoot.add(cu1);
        CompilationUnit cu2 = new CompilationUnit("com.github.javaparser.ast");
        sourceRoot.add(cu2);

        Path templateFile = tempProjectRoot.resolve("bnd.bnd.template");
        Files.write(templateFile, "{exportedPackages}".getBytes());

        generator.generate();

        Path outputFile = tempProjectRoot.resolve("bnd.bnd");
        String content = new String(Files.readAllBytes(outputFile));
        long count = content.split("com\\.github\\.javaparser\\.ast").length - 1;
        assertEquals(1, count, "Package should appear only once");
    }
}

