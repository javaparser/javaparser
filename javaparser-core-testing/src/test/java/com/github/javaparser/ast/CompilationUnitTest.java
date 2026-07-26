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

package com.github.javaparser.ast;

import static com.github.javaparser.utils.CodeGenerationUtils.mavenModuleRoot;
import static org.junit.jupiter.api.Assertions.*;

import com.github.javaparser.JavaParserAdapter;
import com.github.javaparser.StaticJavaParser;
import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import org.junit.jupiter.api.Test;

class CompilationUnitTest {

    private final JavaParserAdapter parser = StaticJavaParser.newParserAdapter();

    @Test
    void issue578TheFirstCommentIsWithinTheCompilationUnit() {
        CompilationUnit compilationUnit =
                parser.parse("// This is my class, with my comment\n" + "class A {\n" + "    static int a;\n" + "}");

        assertEquals(1, compilationUnit.getAllContainedComments().size());
    }

    @Test
    void testGetSourceRoot() throws IOException {
        Path sourceRoot = mavenModuleRoot(CompilationUnitTest.class)
                .resolve(Paths.get("src", "test", "resources"))
                .normalize();
        Path testFile = sourceRoot.resolve(Paths.get("com", "github", "javaparser", "storage", "Z.java"));

        CompilationUnit cu = parser.parse(testFile);
        Path sourceRoot1 = cu.getStorage().get().getSourceRoot();
        assertEquals(sourceRoot, sourceRoot1);
    }

    @Test
    void testGetSourceRootWithBadPackageDeclaration() {
        assertThrows(RuntimeException.class, () -> {
            Path sourceRoot = mavenModuleRoot(CompilationUnitTest.class)
                    .resolve(Paths.get("src", "test", "resources"))
                    .normalize();
            Path testFile = sourceRoot.resolve(Paths.get("com", "github", "javaparser", "storage", "A.java"));
            CompilationUnit cu = parser.parse(testFile);
            cu.getStorage().get().getSourceRoot();
        });
    }

    @Test
    void testGetSourceRootInDefaultPackage() throws IOException {
        Path sourceRoot = mavenModuleRoot(CompilationUnitTest.class)
                .resolve(Paths.get("src", "test", "resources", "com", "github", "javaparser", "storage"))
                .normalize();
        Path testFile = sourceRoot.resolve(Paths.get("B.java"));

        CompilationUnit cu = parser.parse(testFile);
        Path sourceRoot1 = cu.getStorage().get().getSourceRoot();
        assertEquals(sourceRoot, sourceRoot1);
    }

    @Test
    void testGetPrimaryTypeName() throws IOException {
        Path sourceRoot = mavenModuleRoot(CompilationUnitTest.class)
                .resolve(Paths.get("src", "test", "resources"))
                .normalize();
        Path testFile = sourceRoot.resolve(Paths.get("com", "github", "javaparser", "storage", "PrimaryType.java"));
        CompilationUnit cu = parser.parse(testFile);

        assertEquals("PrimaryType", cu.getPrimaryTypeName().get());
    }

    @Test
    void testNoPrimaryTypeName() {
        CompilationUnit cu = parser.parse("class PrimaryType{}");

        assertFalse(cu.getPrimaryTypeName().isPresent());
    }

    @Test
    void testGetPrimaryType() throws IOException {
        Path sourceRoot = mavenModuleRoot(CompilationUnitTest.class)
                .resolve(Paths.get("src", "test", "resources"))
                .normalize();
        Path testFile = sourceRoot.resolve(Paths.get("com", "github", "javaparser", "storage", "PrimaryType.java"));
        CompilationUnit cu = parser.parse(testFile);

        assertEquals("PrimaryType", cu.getPrimaryType().get().getNameAsString());
    }

    @Test
    void testNoPrimaryType() throws IOException {
        Path sourceRoot = mavenModuleRoot(CompilationUnitTest.class)
                .resolve(Paths.get("src", "test", "resources"))
                .normalize();
        Path testFile = sourceRoot.resolve(Paths.get("com", "github", "javaparser", "storage", "PrimaryType2.java"));
        CompilationUnit cu = parser.parse(testFile);

        assertFalse(cu.getPrimaryType().isPresent());
    }
}
