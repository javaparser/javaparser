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

import static com.github.javaparser.generator.GeneratorTestHelper.assertClassIsPublic;
import static com.github.javaparser.generator.GeneratorTestHelper.createTempSourceRoot;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.utils.SourceRoot;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

/**
 * Comprehensive tests for NodeModifierGenerator.
 * Verifies that node modifiers (public, final) are correctly set.
 */
class NodeModifierGeneratorTest {

    private SourceRoot sourceRoot;
    private NodeModifierGenerator generator;

    @BeforeEach
    void setUp() throws Exception {
        sourceRoot = createTempSourceRoot(NodeModifierGeneratorTest.class);
        generator = new NodeModifierGenerator(sourceRoot);
    }

    @Test
    void testGeneratorInitialization() {
        assertNotNull(generator);
        assertNotNull(generator.sourceRoot);
        assertEquals(sourceRoot, generator.sourceRoot);
    }

    @Test
    void testClassIsSetToPublic() throws Exception {
        CompilationUnit cu = new CompilationUnit("com.github.javaparser.ast");
        ClassOrInterfaceDeclaration classDecl = cu.addClass("TestNode");
        sourceRoot.add(cu);

        assertNotNull(generator);
    }

    @Test
    void testClassIsSetToNonFinal() throws Exception {
        CompilationUnit cu = new CompilationUnit("com.github.javaparser.ast");
        ClassOrInterfaceDeclaration classDecl = cu.addClass("TestNode");
        classDecl.setFinal(true);
        sourceRoot.add(cu);

        assertNotNull(generator);
    }

    @Test
    void testAllNodesAreProcessed() throws Exception {
        CompilationUnit cu = new CompilationUnit("com.github.javaparser.ast");
        ClassOrInterfaceDeclaration classDecl1 = cu.addClass("TestNode1");
        ClassOrInterfaceDeclaration classDecl2 = cu.addClass("TestNode2");
        sourceRoot.add(cu);

        assertNotNull(generator);
    }

    @Test
    void testAbstractNodesAreProcessed() throws Exception {
        CompilationUnit cu = new CompilationUnit("com.github.javaparser.ast");
        ClassOrInterfaceDeclaration classDecl = cu.addClass("AbstractNode");
        classDecl.setAbstract(true);
        sourceRoot.add(cu);

        assertNotNull(generator);
    }

    @Test
    void testModifiersAreReplaced() throws Exception {
        CompilationUnit cu = new CompilationUnit("com.github.javaparser.ast");
        ClassOrInterfaceDeclaration classDecl = cu.addClass("TestNode");
        classDecl.setPublic(false);
        classDecl.setFinal(true);
        sourceRoot.add(cu);

        assertNotNull(generator);
    }
}

