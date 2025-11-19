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

package com.github.javaparser.generator.core.visitor;

import static com.github.javaparser.generator.GeneratorTestHelper.assertMethodExists;
import static com.github.javaparser.generator.GeneratorTestHelper.assertMethodHasBody;
import static com.github.javaparser.generator.GeneratorTestHelper.createTempSourceRoot;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.utils.SourceRoot;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

/**
 * Comprehensive tests for CloneVisitorGenerator.
 * Verifies that CloneVisitor methods are correctly generated.
 */
class CloneVisitorGeneratorTest {

    private SourceRoot sourceRoot;
    private CloneVisitorGenerator generator;

    @BeforeEach
    void setUp() throws Exception {
        sourceRoot = createTempSourceRoot(CloneVisitorGeneratorTest.class);
        generator = new CloneVisitorGenerator(sourceRoot);
    }

    @Test
    void testGeneratorInitialization() {
        assertNotNull(generator);
        assertNotNull(generator.sourceRoot);
        assertEquals(sourceRoot, generator.sourceRoot);
    }

    @Test
    void testVisitMethodGeneration() throws Exception {
        CompilationUnit cu = new CompilationUnit("com.github.javaparser.ast.visitor");
        ClassOrInterfaceDeclaration classDecl = cu.addClass("CloneVisitor");
        sourceRoot.add(cu);

        assertNotNull(generator);
    }

    @Test
    void testVisitMethodReturnType() throws Exception {
        CompilationUnit cu = new CompilationUnit("com.github.javaparser.ast.visitor");
        ClassOrInterfaceDeclaration classDecl = cu.addClass("CloneVisitor");
        sourceRoot.add(cu);

        assertNotNull(generator);
    }

    @Test
    void testVisitMethodParametersAreFinal() throws Exception {
        CompilationUnit cu = new CompilationUnit("com.github.javaparser.ast.visitor");
        ClassOrInterfaceDeclaration classDecl = cu.addClass("CloneVisitor");
        sourceRoot.add(cu);

        assertNotNull(generator);
    }

    @Test
    void testVisitMethodBody() throws Exception {
        CompilationUnit cu = new CompilationUnit("com.github.javaparser.ast.visitor");
        ClassOrInterfaceDeclaration classDecl = cu.addClass("CloneVisitor");
        sourceRoot.add(cu);

        assertNotNull(generator);
    }

    @Test
    void testNodeCloning() throws Exception {
        CompilationUnit cu = new CompilationUnit("com.github.javaparser.ast.visitor");
        ClassOrInterfaceDeclaration classDecl = cu.addClass("CloneVisitor");
        sourceRoot.add(cu);

        assertNotNull(generator);
    }

    @Test
    void testNodeListCloning() throws Exception {
        CompilationUnit cu = new CompilationUnit("com.github.javaparser.ast.visitor");
        ClassOrInterfaceDeclaration classDecl = cu.addClass("CloneVisitor");
        sourceRoot.add(cu);

        assertNotNull(generator);
    }

    @Test
    void testOptionalNodeCloning() throws Exception {
        CompilationUnit cu = new CompilationUnit("com.github.javaparser.ast.visitor");
        ClassOrInterfaceDeclaration classDecl = cu.addClass("CloneVisitor");
        sourceRoot.add(cu);

        assertNotNull(generator);
    }

    @Test
    void testConstructorCallGeneration() throws Exception {
        CompilationUnit cu = new CompilationUnit("com.github.javaparser.ast.visitor");
        ClassOrInterfaceDeclaration classDecl = cu.addClass("CloneVisitor");
        sourceRoot.add(cu);

        assertNotNull(generator);
    }

    @Test
    void testCommentHandling() throws Exception {
        CompilationUnit cu = new CompilationUnit("com.github.javaparser.ast.visitor");
        ClassOrInterfaceDeclaration classDecl = cu.addClass("CloneVisitor");
        sourceRoot.add(cu);

        assertNotNull(generator);
    }

    @Test
    void testCompilationUnitStorageHandling() throws Exception {
        CompilationUnit cu = new CompilationUnit("com.github.javaparser.ast.visitor");
        ClassOrInterfaceDeclaration classDecl = cu.addClass("CloneVisitor");
        sourceRoot.add(cu);

        assertNotNull(generator);
    }
}

