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

package com.github.javaparser.ast;

import com.github.javaparser.JavaParser;
import org.junit.Test;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;

import static com.github.javaparser.JavaParser.parse;
import static com.github.javaparser.utils.CodeGenerationUtils.mavenModuleRoot;
import static org.junit.Assert.assertEquals;

public class CompilationUnitTest {
    @Test
    public void issue578TheFirstCommentIsWithinTheCompilationUnit() {
        CompilationUnit compilationUnit = parse("// This is my class, with my comment\n" +
                "class A {\n" +
                "    static int a;\n" +
                "}");

        assertEquals(1, compilationUnit.getAllContainedComments().size());
    }

    @Test
    public void testGetSourceRoot() throws IOException {
        Path sourceRoot = mavenModuleRoot(CompilationUnitTest.class).resolve(Paths.get("src", "test", "resources")).normalize();
        Path testFile = sourceRoot.resolve(Paths.get("com", "github", "javaparser", "storage", "Z.java"));

        CompilationUnit cu = parse(testFile);
        Path sourceRoot1 = cu.getStorage().get().getSourceRoot();
        assertEquals(sourceRoot, sourceRoot1);
    }

    @Test(expected = RuntimeException.class)
    public void testGetSourceRootWithBadPackageDeclaration() throws IOException {
        Path sourceRoot = mavenModuleRoot(CompilationUnitTest.class).resolve(Paths.get("src", "test", "resources")).normalize();
        Path testFile = sourceRoot.resolve(Paths.get("com", "github", "javaparser", "storage", "A.java"));

        CompilationUnit cu = parse(testFile);
        cu.getStorage().get().getSourceRoot();
    }

    @Test
    public void testGetSourceRootInDefaultPackage() throws IOException {
        Path sourceRoot = mavenModuleRoot(CompilationUnitTest.class).resolve(Paths.get("src", "test", "resources", "com", "github", "javaparser", "storage")).normalize();
        Path testFile = sourceRoot.resolve(Paths.get("B.java"));

        CompilationUnit cu = parse(testFile);
        Path sourceRoot1 = cu.getStorage().get().getSourceRoot();
        assertEquals(sourceRoot, sourceRoot1);
    }
    
    @Test
    public void testGetPrimaryTypeName() throws IOException {
        Path sourceRoot = mavenModuleRoot(CompilationUnitTest.class).resolve(Paths.get("src", "test", "resources")).normalize();
        Path testFile = sourceRoot.resolve(Paths.get("com", "github", "javaparser", "storage", "PrimaryType.java"));
        CompilationUnit cu = JavaParser.parse(testFile);
        
        assertEquals("PrimaryType", cu.getPrimaryTypeName().get());
    }

    @Test
    public void testNoPrimaryTypeName() {
        CompilationUnit cu = JavaParser.parse("class PrimaryType{}");

        assertEquals(false, cu.getPrimaryTypeName().isPresent());
    }
    @Test
    public void testGetPrimaryType() throws IOException {
        Path sourceRoot = mavenModuleRoot(CompilationUnitTest.class).resolve(Paths.get("src", "test", "resources")).normalize();
        Path testFile = sourceRoot.resolve(Paths.get("com", "github", "javaparser", "storage", "PrimaryType.java"));
        CompilationUnit cu = JavaParser.parse(testFile);

        assertEquals("PrimaryType",     cu.getPrimaryType().get().getNameAsString());
    }

    @Test
    public void testNoPrimaryType() throws IOException {
        Path sourceRoot = mavenModuleRoot(CompilationUnitTest.class).resolve(Paths.get("src", "test", "resources")).normalize();
        Path testFile = sourceRoot.resolve(Paths.get("com", "github", "javaparser", "storage", "PrimaryType2.java"));
        CompilationUnit cu = JavaParser.parse(testFile);

        assertEquals(false, cu.getPrimaryType().isPresent());
    }

}
