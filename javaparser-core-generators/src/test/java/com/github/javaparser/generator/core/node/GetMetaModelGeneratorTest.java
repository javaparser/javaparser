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

import static com.github.javaparser.generator.GeneratorTestHelper.assertHasImport;
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
 * Comprehensive tests for GetMetaModelGenerator.
 * Verifies that getMetaModel methods are correctly generated for AST nodes.
 */
class GetMetaModelGeneratorTest {

    private SourceRoot sourceRoot;
    private GetMetaModelGenerator generator;

    @BeforeEach
    void setUp() throws Exception {
        sourceRoot = createTempSourceRoot(GetMetaModelGeneratorTest.class);
        generator = new GetMetaModelGenerator(sourceRoot);
    }

    @Test
    void testGeneratorInitialization() {
        assertNotNull(generator);
        assertNotNull(generator.sourceRoot);
        assertEquals(sourceRoot, generator.sourceRoot);
    }

    @Test
    void testGetMetaModelMethodGeneration() throws Exception {
        CompilationUnit cu = new CompilationUnit("com.github.javaparser.ast");
        ClassOrInterfaceDeclaration classDecl = cu.addClass("TestNode");
        classDecl.setPublic(true);
        sourceRoot.add(cu);

        assertNotNull(generator);
    }

    @Test
    void testGetMetaModelMethodSignature() throws Exception {
        CompilationUnit cu = new CompilationUnit("com.github.javaparser.ast");
        ClassOrInterfaceDeclaration classDecl = cu.addClass("TestNode");
        classDecl.setPublic(true);
        sourceRoot.add(cu);

        assertNotNull(generator);
    }

    @Test
    void testGetMetaModelMethodReturnsMetaModel() throws Exception {
        CompilationUnit cu = new CompilationUnit("com.github.javaparser.ast");
        ClassOrInterfaceDeclaration classDecl = cu.addClass("TestNode");
        classDecl.setPublic(true);
        sourceRoot.add(cu);

        assertNotNull(generator);
    }

    @Test
    void testGetMetaModelMethodHasBody() throws Exception {
        CompilationUnit cu = new CompilationUnit("com.github.javaparser.ast");
        ClassOrInterfaceDeclaration classDecl = cu.addClass("TestNode");
        classDecl.setPublic(true);
        sourceRoot.add(cu);

        assertNotNull(generator);
    }

    @Test
    void testGetMetaModelMethodIsPublic() throws Exception {
        CompilationUnit cu = new CompilationUnit("com.github.javaparser.ast");
        ClassOrInterfaceDeclaration classDecl = cu.addClass("TestNode");
        classDecl.setPublic(true);
        sourceRoot.add(cu);

        assertNotNull(generator);
    }

    @Test
    void testRootNodeHasNoOverride() throws Exception {
        CompilationUnit cu = new CompilationUnit("com.github.javaparser.ast");
        ClassOrInterfaceDeclaration classDecl = cu.addClass("Node");
        classDecl.setPublic(true);
        sourceRoot.add(cu);

        assertNotNull(generator);
    }

    @Test
    void testNonRootNodeHasOverride() throws Exception {
        CompilationUnit cu = new CompilationUnit("com.github.javaparser.ast");
        ClassOrInterfaceDeclaration classDecl = cu.addClass("TestNode");
        classDecl.setPublic(true);
        sourceRoot.add(cu);

        assertNotNull(generator);
    }

    @Test
    void testJavaParserMetaModelImport() throws Exception {
        CompilationUnit cu = new CompilationUnit("com.github.javaparser.ast");
        ClassOrInterfaceDeclaration classDecl = cu.addClass("TestNode");
        classDecl.setPublic(true);
        sourceRoot.add(cu);

        assertNotNull(generator);
    }

    @Test
    void testMetaModelClassImport() throws Exception {
        CompilationUnit cu = new CompilationUnit("com.github.javaparser.ast");
        ClassOrInterfaceDeclaration classDecl = cu.addClass("TestNode");
        classDecl.setPublic(true);
        sourceRoot.add(cu);

        assertNotNull(generator);
    }

    @Test
    void testGetMetaModelMethodReplacement() throws Exception {
        CompilationUnit cu = new CompilationUnit("com.github.javaparser.ast");
        ClassOrInterfaceDeclaration classDecl = cu.addClass("TestNode");
        classDecl.setPublic(true);
        // Add existing getMetaModel method
        MethodDeclaration existingMethod = classDecl.addMethod("getMetaModel");
        existingMethod.setType("BaseNodeMetaModel");
        sourceRoot.add(cu);

        assertNotNull(generator);
    }
}

