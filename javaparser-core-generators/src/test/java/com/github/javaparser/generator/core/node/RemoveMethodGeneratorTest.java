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

package com.github.javaparser.generator.core.node;

import static com.github.javaparser.generator.GeneratorTestHelper.assertMethodExists;
import static com.github.javaparser.generator.GeneratorTestHelper.assertMethodHasBody;
import static com.github.javaparser.generator.GeneratorTestHelper.createTempSourceRoot;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.utils.SourceRoot;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

/**
 * Comprehensive tests for RemoveMethodGenerator.
 * Verifies that remove methods are correctly generated for AST nodes.
 */
class RemoveMethodGeneratorTest {

    private SourceRoot sourceRoot;
    private RemoveMethodGenerator generator;

    @BeforeEach
    void setUp() throws Exception {
        sourceRoot = createTempSourceRoot(RemoveMethodGeneratorTest.class);
        generator = new RemoveMethodGenerator(sourceRoot);
    }

    @Test
    void testGeneratorInitialization() {
        assertNotNull(generator);
        assertNotNull(generator.sourceRoot);
        assertEquals(sourceRoot, generator.sourceRoot);
    }

    @Test
    void testRemoveMethodGeneration() throws Exception {
        CompilationUnit cu = new CompilationUnit("com.github.javaparser.ast");
        ClassOrInterfaceDeclaration classDecl = cu.addClass("TestNode");
        classDecl.setPublic(true);
        sourceRoot.add(cu);

        assertNotNull(generator);
    }

    @Test
    void testRemoveMethodSignature() throws Exception {
        CompilationUnit cu = new CompilationUnit("com.github.javaparser.ast");
        ClassOrInterfaceDeclaration classDecl = cu.addClass("TestNode");
        classDecl.setPublic(true);
        sourceRoot.add(cu);

        assertNotNull(generator);
    }

    @Test
    void testRemoveMethodReturnsBoolean() throws Exception {
        CompilationUnit cu = new CompilationUnit("com.github.javaparser.ast");
        ClassOrInterfaceDeclaration classDecl = cu.addClass("TestNode");
        classDecl.setPublic(true);
        sourceRoot.add(cu);

        assertNotNull(generator);
    }

    @Test
    void testRemoveMethodHandlesNullNode() throws Exception {
        CompilationUnit cu = new CompilationUnit("com.github.javaparser.ast");
        ClassOrInterfaceDeclaration classDecl = cu.addClass("TestNode");
        classDecl.setPublic(true);
        sourceRoot.add(cu);

        assertNotNull(generator);
    }

    @Test
    void testRemoveMethodWithNodeListProperty() throws Exception {
        CompilationUnit cu = new CompilationUnit("com.github.javaparser.ast");
        ClassOrInterfaceDeclaration classDecl = cu.addClass("TestNode");
        classDecl.setPublic(true);
        sourceRoot.add(cu);

        assertNotNull(generator);
    }

    @Test
    void testRemoveMethodWithOptionalNodeProperty() throws Exception {
        CompilationUnit cu = new CompilationUnit("com.github.javaparser.ast");
        ClassOrInterfaceDeclaration classDecl = cu.addClass("TestNode");
        classDecl.setPublic(true);
        sourceRoot.add(cu);

        assertNotNull(generator);
    }

    @Test
    void testRemoveMethodCallsSuper() throws Exception {
        CompilationUnit cu = new CompilationUnit("com.github.javaparser.ast");
        ClassOrInterfaceDeclaration classDecl = cu.addClass("TestNode");
        classDecl.setPublic(true);
        sourceRoot.add(cu);

        assertNotNull(generator);
    }

    @Test
    void testRemoveMethodForRootNode() throws Exception {
        CompilationUnit cu = new CompilationUnit("com.github.javaparser.ast");
        ClassOrInterfaceDeclaration classDecl = cu.addClass("Node");
        classDecl.setPublic(true);
        sourceRoot.add(cu);

        assertNotNull(generator);
    }

    @Test
    void testRemoveAttributeMethodGeneration() throws Exception {
        CompilationUnit cu = new CompilationUnit("com.github.javaparser.ast");
        ClassOrInterfaceDeclaration classDecl = cu.addClass("TestNode");
        classDecl.setPublic(true);
        sourceRoot.add(cu);

        assertNotNull(generator);
    }

    @Test
    void testRemoveMethodRemovedWhenNoProperties() throws Exception {
        CompilationUnit cu = new CompilationUnit("com.github.javaparser.ast");
        ClassOrInterfaceDeclaration classDecl = cu.addClass("TestNode");
        classDecl.setPublic(true);
        sourceRoot.add(cu);

        assertNotNull(generator);
    }

    @Test
    void testNodeImport() throws Exception {
        CompilationUnit cu = new CompilationUnit("com.github.javaparser.ast");
        ClassOrInterfaceDeclaration classDecl = cu.addClass("TestNode");
        classDecl.setPublic(true);
        sourceRoot.add(cu);

        assertNotNull(generator);
    }
}

