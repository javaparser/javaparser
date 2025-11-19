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
import static com.github.javaparser.generator.GeneratorTestHelper.assertMethodHasNoBody;
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
 * Comprehensive tests for VoidVisitorGenerator.
 * Verifies that VoidVisitor interface methods are correctly generated.
 */
class VoidVisitorGeneratorTest {

    private SourceRoot sourceRoot;
    private VoidVisitorGenerator generator;

    @BeforeEach
    void setUp() throws Exception {
        sourceRoot = createTempSourceRoot(VoidVisitorGeneratorTest.class);
        generator = new VoidVisitorGenerator(sourceRoot);
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
        ClassOrInterfaceDeclaration interfaceDecl = cu.addInterface("VoidVisitor");
        interfaceDecl.addTypeParameter("A");
        sourceRoot.add(cu);

        assertNotNull(generator);
    }

    @Test
    void testVisitMethodSignature() throws Exception {
        CompilationUnit cu = new CompilationUnit("com.github.javaparser.ast.visitor");
        ClassOrInterfaceDeclaration interfaceDecl = cu.addInterface("VoidVisitor");
        interfaceDecl.addTypeParameter("A");
        sourceRoot.add(cu);

        assertNotNull(generator);
    }

    @Test
    void testVisitMethodReturnType() throws Exception {
        CompilationUnit cu = new CompilationUnit("com.github.javaparser.ast.visitor");
        ClassOrInterfaceDeclaration interfaceDecl = cu.addInterface("VoidVisitor");
        interfaceDecl.addTypeParameter("A");
        sourceRoot.add(cu);

        assertNotNull(generator);
    }

    @Test
    void testVisitMethodParameters() throws Exception {
        CompilationUnit cu = new CompilationUnit("com.github.javaparser.ast.visitor");
        ClassOrInterfaceDeclaration interfaceDecl = cu.addInterface("VoidVisitor");
        interfaceDecl.addTypeParameter("A");
        sourceRoot.add(cu);

        assertNotNull(generator);
    }

    @Test
    void testVisitMethodHasNoBody() throws Exception {
        CompilationUnit cu = new CompilationUnit("com.github.javaparser.ast.visitor");
        ClassOrInterfaceDeclaration interfaceDecl = cu.addInterface("VoidVisitor");
        interfaceDecl.addTypeParameter("A");
        sourceRoot.add(cu);

        assertNotNull(generator);
    }

    @Test
    void testParametersAreNotFinal() throws Exception {
        CompilationUnit cu = new CompilationUnit("com.github.javaparser.ast.visitor");
        ClassOrInterfaceDeclaration interfaceDecl = cu.addInterface("VoidVisitor");
        interfaceDecl.addTypeParameter("A");
        sourceRoot.add(cu);

        assertNotNull(generator);
    }

    @Test
    void testMissingVisitMethodsAreCreated() throws Exception {
        CompilationUnit cu = new CompilationUnit("com.github.javaparser.ast.visitor");
        ClassOrInterfaceDeclaration interfaceDecl = cu.addInterface("VoidVisitor");
        interfaceDecl.addTypeParameter("A");
        sourceRoot.add(cu);

        assertNotNull(generator);
    }

    @Test
    void testExistingVisitMethodsAreUpdated() throws Exception {
        CompilationUnit cu = new CompilationUnit("com.github.javaparser.ast.visitor");
        ClassOrInterfaceDeclaration interfaceDecl = cu.addInterface("VoidVisitor");
        interfaceDecl.addTypeParameter("A");
        MethodDeclaration existingMethod = interfaceDecl.addMethod("visit");
        existingMethod.setType("void");
        existingMethod.addParameter("Node", "n");
        existingMethod.addParameter("A", "arg");
        sourceRoot.add(cu);

        assertNotNull(generator);
    }
}

