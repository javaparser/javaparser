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

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.fail;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.printer.DefaultPrettyPrinter;
import com.github.javaparser.utils.SourceRoot;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;
import java.util.Optional;

/**
 * Helper utility class for testing generators.
 * Provides common functionality for setting up test environments,
 * comparing generated code, and verifying generator outputs.
 */
public final class GeneratorTestHelper {

    private GeneratorTestHelper() {
        // Utility class - prevent instantiation
    }

    /**
     * Creates a temporary source root for testing generators.
     *
     * @param testClass The test class requesting the source root
     * @return A SourceRoot pointing to a temporary directory
     */
    public static SourceRoot createTempSourceRoot(Class<?> testClass) throws Exception {
        Path tempDir = Files.createTempDirectory("javaparser-generator-test-" + testClass.getSimpleName());
        tempDir.toFile().deleteOnExit();
        return new SourceRoot(tempDir);
    }

    /**
     * Creates a test source root from resources directory.
     *
     * @param testClass The test class
     * @param subdirectory The subdirectory within the test resources
     * @return A SourceRoot pointing to the test resources
     */
    public static SourceRoot createTestSourceRoot(Class<?> testClass, String subdirectory) {
        String[] packageParts = testClass.getCanonicalName().split("\\.");
        Path testPath = Paths.get("src", "test", "resources");
        for (String part : packageParts) {
            testPath = testPath.resolve(part);
        }
        testPath = testPath.resolve(subdirectory);
        return new SourceRoot(testPath);
    }

    /**
     * Compares generated code with expected code.
     *
     * @param generated The generated compilation unit
     * @param expected The expected compilation unit
     * @param message Optional message to include in assertion failure
     */
    public static void assertCodeEquals(CompilationUnit generated, CompilationUnit expected, String message) {
        DefaultPrettyPrinter printer = new DefaultPrettyPrinter();
        String generatedCode = printer.print(generated);
        String expectedCode = printer.print(expected);

        if (!expectedCode.equals(generatedCode)) {
            System.out.println("Expected:");
            System.out.println("####");
            System.out.println(expectedCode);
            System.out.println("####");
            System.out.println("Actual:");
            System.out.println("####");
            System.out.println(generatedCode);
            System.out.println("####");
            fail(message != null ? message : "Generated code doesn't match expected code.");
        }
    }

    /**
     * Compares generated code with expected code.
     *
     * @param generated The generated compilation unit
     * @param expected The expected compilation unit
     */
    public static void assertCodeEquals(CompilationUnit generated, CompilationUnit expected) {
        assertCodeEquals(generated, expected, null);
    }

    /**
     * Verifies that a compilation unit contains a specific class.
     *
     * @param cu The compilation unit to check
     * @param className The name of the class to find
     * @return The found class declaration
     */
    public static ClassOrInterfaceDeclaration assertClassExists(CompilationUnit cu, String className) {
        Optional<ClassOrInterfaceDeclaration> classOpt = cu.getClassByName(className);
        assertTrue(classOpt.isPresent(), "Class " + className + " should exist in compilation unit");
        return classOpt.get();
    }

    /**
     * Verifies that a class contains a method with the given signature.
     *
     * @param classDecl The class declaration to check
     * @param methodName The name of the method
     * @param parameterTypes The parameter types
     * @return The found method declaration
     */
    public static MethodDeclaration assertMethodExists(
            ClassOrInterfaceDeclaration classDecl, String methodName, String... parameterTypes) {
        List<MethodDeclaration> methods = classDecl.getMethodsByName(methodName);
        assertTrue(!methods.isEmpty(), "Method " + methodName + " should exist in class");

        for (MethodDeclaration method : methods) {
            if (method.getParameters().size() == parameterTypes.length) {
                boolean matches = true;
                for (int i = 0; i < parameterTypes.length; i++) {
                    if (!method.getParameter(i).getType().asString().equals(parameterTypes[i])) {
                        matches = false;
                        break;
                    }
                }
                if (matches) {
                    return method;
                }
            }
        }

        fail("Method " + methodName + " with expected signature not found");
        return null; // Never reached
    }

    /**
     * Verifies that a method has the @Generated annotation.
     *
     * @param method The method declaration to check
     */
    public static void assertHasGeneratedAnnotation(MethodDeclaration method) {
        assertTrue(
                method.getAnnotations().stream()
                        .anyMatch(a -> a.getNameAsString().equals("Generated")),
                "Method should have @Generated annotation");
    }

    /**
     * Verifies that a method has the @Override annotation.
     *
     * @param method The method declaration to check
     */
    public static void assertHasOverrideAnnotation(MethodDeclaration method) {
        assertTrue(
                method.getAnnotations().stream()
                        .anyMatch(a -> a.getNameAsString().equals("Override")),
                "Method should have @Override annotation");
    }

    /**
     * Verifies that a compilation unit has a specific import.
     *
     * @param cu The compilation unit to check
     * @param importName The import name to check for
     */
    public static void assertHasImport(CompilationUnit cu, String importName) {
        assertTrue(
                cu.getImports().stream()
                        .anyMatch(imp -> imp.getNameAsString().equals(importName)),
                "Compilation unit should have import: " + importName);
    }

    /**
     * Compares all compilation units from two source roots.
     *
     * @param generatedRoot The source root with generated code
     * @param expectedRoot The source root with expected code
     */
    public static void assertSourceRootsEqual(SourceRoot generatedRoot, SourceRoot expectedRoot) throws Exception {
        expectedRoot.tryToParse();
        List<CompilationUnit> generatedCus = generatedRoot.getCompilationUnits();
        List<CompilationUnit> expectedCus = expectedRoot.getCompilationUnits();

        assertEquals(expectedCus.size(), generatedCus.size(), "Number of compilation units should match");

        for (int i = 0; i < generatedCus.size(); i++) {
            assertCodeEquals(generatedCus.get(i), expectedCus.get(i));
        }
    }

    /**
     * Creates a simple test class compilation unit.
     *
     * @param packageName The package name
     * @param className The class name
     * @return A compilation unit with a simple class
     */
    public static CompilationUnit createSimpleTestClass(String packageName, String className) {
        CompilationUnit cu = new CompilationUnit(packageName);
        ClassOrInterfaceDeclaration classDecl = cu.addClass(className);
        classDecl.setPublic(true);
        return cu;
    }

    /**
     * Verifies that a class is public.
     *
     * @param classDecl The class declaration to check
     */
    public static void assertClassIsPublic(ClassOrInterfaceDeclaration classDecl) {
        assertTrue(classDecl.isPublic(), "Class should be public");
    }

    /**
     * Verifies that a method is public.
     *
     * @param method The method declaration to check
     */
    public static void assertMethodIsPublic(MethodDeclaration method) {
        assertTrue(method.isPublic(), "Method should be public");
    }

    /**
     * Verifies that a method has a body.
     *
     * @param method The method declaration to check
     */
    public static void assertMethodHasBody(MethodDeclaration method) {
        assertTrue(method.getBody().isPresent(), "Method should have a body");
    }

    /**
     * Verifies that a method does not have a body (is abstract or interface method).
     *
     * @param method The method declaration to check
     */
    public static void assertMethodHasNoBody(MethodDeclaration method) {
        assertTrue(!method.getBody().isPresent(), "Method should not have a body");
    }
}

