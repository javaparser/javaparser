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

package com.github.javaparser.generator;

import static com.github.javaparser.generator.GeneratorTestHelper.assertHasGeneratedAnnotation;
import static com.github.javaparser.generator.GeneratorTestHelper.assertHasOverrideAnnotation;
import static com.github.javaparser.generator.GeneratorTestHelper.assertMethodExists;
import static com.github.javaparser.generator.GeneratorTestHelper.createSimpleTestClass;
import static com.github.javaparser.generator.GeneratorTestHelper.createTempSourceRoot;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.StringLiteralExpr;
import com.github.javaparser.utils.SourceRoot;
import java.util.List;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

/**
 * Comprehensive tests for the base Generator class.
 * Tests annotation handling, method replacement, and utility methods.
 */
class GeneratorTest {

    private SourceRoot sourceRoot;
    private TestGenerator generator;

    @BeforeEach
    void setUp() throws Exception {
        sourceRoot = createTempSourceRoot(GeneratorTest.class);
        generator = new TestGenerator(sourceRoot);
    }

    @Test
    void testGeneratorInitialization() {
        assertNotNull(generator);
        assertNotNull(generator.sourceRoot);
        assertEquals(sourceRoot, generator.sourceRoot);
    }

    @Test
    void testAnnotateGenerated() {
        CompilationUnit cu = createSimpleTestClass("test", "TestClass");
        ClassOrInterfaceDeclaration classDecl = cu.getClassByName("TestClass").get();
        MethodDeclaration method = classDecl.addMethod("testMethod");

        generator.testAnnotateGenerated(method);

        assertHasGeneratedAnnotation(method);
        assertTrue(
                method.getAnnotationByName("Generated").isPresent(),
                "Method should have @Generated annotation");
        StringLiteralExpr annotationValue =
                method.getAnnotationByName("Generated").get().asSingleMemberAnnotationExpr().getMemberValue()
                        .asStringLiteralExpr();
        assertEquals(TestGenerator.class.getName(), annotationValue.getValue());
    }

    @Test
    void testAnnotateSuppressWarnings() {
        CompilationUnit cu = createSimpleTestClass("test", "TestClass");
        ClassOrInterfaceDeclaration classDecl = cu.getClassByName("TestClass").get();
        MethodDeclaration method = classDecl.addMethod("testMethod");

        generator.testAnnotateSuppressWarnings(method);

        assertTrue(
                method.getAnnotationByName("SuppressWarnings").isPresent(),
                "Method should have @SuppressWarnings annotation");
    }

    @Test
    void testAnnotateOverridden() {
        CompilationUnit cu = createSimpleTestClass("test", "TestClass");
        ClassOrInterfaceDeclaration classDecl = cu.getClassByName("TestClass").get();
        MethodDeclaration method = classDecl.addMethod("toString");

        generator.testAnnotateOverridden(method);

        assertHasOverrideAnnotation(method);
    }

    @Test
    void testAddOrReplaceWhenSameSignature_AddNewMethod() {
        CompilationUnit cu = createSimpleTestClass("test", "TestClass");
        ClassOrInterfaceDeclaration classDecl = cu.getClassByName("TestClass").get();
        MethodDeclaration newMethod = classDecl.addMethod("testMethod").setType("void");

        generator.testAddOrReplaceWhenSameSignature(classDecl, newMethod);

        List<MethodDeclaration> methods = classDecl.getMethodsByName("testMethod");
        assertEquals(1, methods.size());
        assertHasGeneratedAnnotation(methods.get(0));
    }

    @Test
    void testAddOrReplaceWhenSameSignature_ReplaceExistingMethod() {
        CompilationUnit cu = createSimpleTestClass("test", "TestClass");
        ClassOrInterfaceDeclaration classDecl = cu.getClassByName("TestClass").get();
        MethodDeclaration existingMethod = classDecl.addMethod("testMethod").setType("void");
        existingMethod.setBody("return;");
        existingMethod.setJavadocComment("Old javadoc");

        MethodDeclaration newMethod = classDecl.addMethod("testMethod").setType("void");
        newMethod.setBody("return;");

        generator.testAddOrReplaceWhenSameSignature(classDecl, newMethod);

        List<MethodDeclaration> methods = classDecl.getMethodsByName("testMethod");
        assertEquals(1, methods.size());
        assertTrue(methods.get(0).getJavadocComment().isPresent());
        assertEquals("Old javadoc", methods.get(0).getJavadocComment().get().getContent());
    }

    @Test
    void testReplaceWhenSameSignature_ExistingMethod() {
        CompilationUnit cu = createSimpleTestClass("test", "TestClass");
        ClassOrInterfaceDeclaration classDecl = cu.getClassByName("TestClass").get();
        classDecl.addMethod("testMethod").setType("void");

        MethodDeclaration replacement = classDecl.addMethod("testMethod").setType("void");
        replacement.setBody("return;");

        generator.testReplaceWhenSameSignature(classDecl, replacement);

        List<MethodDeclaration> methods = classDecl.getMethodsByName("testMethod");
        assertEquals(1, methods.size());
    }

    @Test
    void testReplaceWhenSameSignature_MissingMethodThrowsException() {
        CompilationUnit cu = createSimpleTestClass("test", "TestClass");
        ClassOrInterfaceDeclaration classDecl = cu.getClassByName("TestClass").get();
        MethodDeclaration newMethod = classDecl.addMethod("testMethod").setType("void");

        assertThrows(AssertionError.class, () -> generator.testReplaceWhenSameSignature(classDecl, newMethod));
    }

    @Test
    void testRemoveMethodWithSameSignature() {
        CompilationUnit cu = createSimpleTestClass("test", "TestClass");
        ClassOrInterfaceDeclaration classDecl = cu.getClassByName("TestClass").get();
        classDecl.addMethod("testMethod").setType("void");
        classDecl.addMethod("testMethod").setType("void").addParameter("int", "param");

        MethodDeclaration toRemove = classDecl.addMethod("testMethod").setType("void");

        generator.testRemoveMethodWithSameSignature(classDecl, toRemove);

        List<MethodDeclaration> methods = classDecl.getMethodsByName("testMethod");
        assertEquals(1, methods.size());
        assertEquals(1, methods.get(0).getParameters().size());
    }

    @Test
    void testAnnotationReplacement() {
        CompilationUnit cu = createSimpleTestClass("test", "TestClass");
        ClassOrInterfaceDeclaration classDecl = cu.getClassByName("TestClass").get();
        MethodDeclaration method = classDecl.addMethod("testMethod");
        method.addMarkerAnnotation("Generated");

        generator.testAnnotateGenerated(method);

        List<MethodDeclaration> methods = classDecl.getMethodsByName("testMethod");
        assertEquals(1, methods.size());
        assertTrue(methods.get(0).getAnnotationByName("Generated").isPresent());
    }

    @Test
    void testMultipleAnnotations() {
        CompilationUnit cu = createSimpleTestClass("test", "TestClass");
        ClassOrInterfaceDeclaration classDecl = cu.getClassByName("TestClass").get();
        MethodDeclaration method = classDecl.addMethod("testMethod");

        generator.testAnnotateGenerated(method);
        generator.testAnnotateSuppressWarnings(method);
        generator.testAnnotateOverridden(method);

        assertTrue(method.getAnnotationByName("Generated").isPresent());
        assertTrue(method.getAnnotationByName("SuppressWarnings").isPresent());
        assertTrue(method.getAnnotationByName("Override").isPresent());
    }

    @Test
    void testImportAddition() {
        CompilationUnit cu = createSimpleTestClass("test", "TestClass");
        ClassOrInterfaceDeclaration classDecl = cu.getClassByName("TestClass").get();
        MethodDeclaration method = classDecl.addMethod("testMethod");

        generator.testAnnotateGenerated(method);

        assertTrue(
                cu.getImports().stream()
                        .anyMatch(imp -> imp.getNameAsString().equals("com.github.javaparser.ast.Generated")));
    }

    /**
     * Test implementation of Generator for testing purposes.
     */
    private static class TestGenerator extends Generator {
        TestGenerator(SourceRoot sourceRoot) {
            super(sourceRoot);
        }

        @Override
        public void generate() throws Exception {
            // Empty implementation for testing
        }

        void testAnnotateGenerated(MethodDeclaration method) {
            annotateGenerated(method);
        }

        void testAnnotateSuppressWarnings(MethodDeclaration method) {
            annotateSuppressWarnings(method);
        }

        void testAnnotateOverridden(MethodDeclaration method) {
            annotateOverridden(method);
        }

        void testAddOrReplaceWhenSameSignature(
                ClassOrInterfaceDeclaration classDecl, MethodDeclaration method) {
            addOrReplaceWhenSameSignature(classDecl, method);
        }

        void testReplaceWhenSameSignature(ClassOrInterfaceDeclaration classDecl, MethodDeclaration method) {
            replaceWhenSameSignature(classDecl, method);
        }

        void testRemoveMethodWithSameSignature(ClassOrInterfaceDeclaration classDecl, MethodDeclaration method) {
            removeMethodWithSameSignature(classDecl, method);
        }
    }
}

