/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2023 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.resolution.typesolvers;

import com.github.javaparser.resolution.TypeSolver;
import org.junit.jupiter.api.Test;

import java.io.File;
import java.io.IOException;
import java.nio.file.Paths;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

class TypeSolverBuilderTest {

    private final TypeSolverBuilder typeSolverBuilder = new TypeSolverBuilder();

    /**
     * Build a new type solver without any configuration,
     * should throw an IllegalStateException.
     */
    @Test
    void testBuild_withoutConfiguration() {
        assertThrows(IllegalStateException.class, typeSolverBuilder::build);
    }

    /**
     * Build a new type solve with a single configuration,
     * should return that configuration.
     */
    @Test
    void testBuild_withASingleTypeSolver() {
        // Prepare
        TypeSolver typeSolverToRegister = mock(TypeSolver.class);

        // Execute
        TypeSolver createdTypeSolver = typeSolverBuilder.with(typeSolverToRegister).build();

        // Assert
        assertEquals(typeSolverToRegister, createdTypeSolver);
    }

    /**
     * When multiple type solver are registered, they should be
     * attached to the same parent.
     */
    @Test
    void testBuild_withMultipleTypeSolver() {
        // Prepare
        TypeSolver typeSolverA = mock(TypeSolver.class);
        TypeSolver typeSolverB = mock(TypeSolver.class);

        // Execute
        TypeSolver createdTypeSolver = typeSolverBuilder
                .with(typeSolverA)
                .with(typeSolverB)
                .build();

        // Verify
        verify(typeSolverA).setParent(createdTypeSolver);
        verifyNoMoreInteractions(typeSolverA);

        verify(typeSolverB).setParent(createdTypeSolver);
        verifyNoMoreInteractions(typeSolverB);
    }

    /**
     * When build is set to include the current JRE,
     * only the JRE types should be solved.
     */
    @Test
    void testBuild_withCurrentJREConfiguration() {
        // Execute
        TypeSolver createdTypeSolver = typeSolverBuilder
                .withCurrentJRE()
                .build();

        // Assert
        assertIsSolved(createdTypeSolver, "java.lang.String");
        assertNotSolved(createdTypeSolver, "com.github.javaparser.ast.Node");
        assertNotSolved(createdTypeSolver, "com.example.a.non.existing.Class");
    }

    /**
     * When build is set to include the class loader,
     * JRE types and other classes defined in the current
     * class loader should be solved.
     */
    @Test
    void testBuild_withCurrentClassloaderConfiguration() {
        // Execute
        TypeSolver createdTypeSolver = typeSolverBuilder
                .withCurrentClassloader()
                .build();

        // Assert
        assertIsSolved(createdTypeSolver, "java.lang.String");
        assertIsSolved(createdTypeSolver, "com.github.javaparser.ast.Node");
        assertNotSolved(createdTypeSolver, "com.example.a.non.existing.Class");
    }

    /**
     * When build is set to include a external JAR from a String,
     * the classes defined inside the file should be solved.
     */
    @Test
    void testBuild_withJARConfiguration_fromString() throws IOException {

        // Execute
        TypeSolver createdTypeSolver = typeSolverBuilder
                .withJAR("src/test/resources/junit-4.8.1.jar")
                .build();

        // Assert
        assertIsSolved(createdTypeSolver, "org.junit.Test");
        assertNotSolved(createdTypeSolver, "com.example.a.non.existing.Class");
    }

    /**
     * When build is set to include a external JAR from a Path,
     * the classes defined inside the file should be solved.
     */
    @Test
    void testBuild_withJARConfiguration_fromPath() throws IOException {

        // Execute
        TypeSolver createdTypeSolver = typeSolverBuilder
                .withJAR(Paths.get("src/test/resources/junit-4.8.1.jar"))
                .build();

        // Assert
        assertIsSolved(createdTypeSolver, "org.junit.Test");
        assertNotSolved(createdTypeSolver, "com.example.a.non.existing.Class");
    }

    /**
     * When build is set to include a external JAR from a File,
     * the classes defined inside the file should be solved.
     */
    @Test
    void testBuild_withJARConfiguration_fromFile() throws IOException {

        // Execute
        TypeSolver createdTypeSolver = typeSolverBuilder
                .withJAR(new File("src/test/resources/junit-4.8.1.jar"))
                .build();

        // Assert
        assertIsSolved(createdTypeSolver, "org.junit.Test");
        assertNotSolved(createdTypeSolver, "com.example.a.non.existing.Class");
    }

    /**
     * When build is set to include a external AAR from a String,
     * the classes defined inside the file should be solved.
     */
    @Test
    void testBuild_withAARConfiguration_fromString() throws IOException {

        // Execute
        TypeSolver createdTypeSolver = typeSolverBuilder
                .withAAR("src/test/resources/aars/support-compat-24.2.0.aar")
                .build();

        // Assert
        assertIsSolved(createdTypeSolver, "android.support.v4.app.ActivityCompat");
        assertNotSolved(createdTypeSolver, "com.example.a.non.existing.Class");
    }

    /**
     * When build is set to include a external AAR from a Path,
     * the classes defined inside the file should be solved.
     */
    @Test
    void testBuild_withAARConfiguration_fromPath() throws IOException {

        // Execute
        TypeSolver createdTypeSolver = typeSolverBuilder
                .withAAR(Paths.get("src/test/resources/aars/support-compat-24.2.0.aar"))
                .build();

        // Assert
        assertIsSolved(createdTypeSolver, "android.support.v4.app.ActivityCompat");
        assertNotSolved(createdTypeSolver, "com.example.a.non.existing.Class");
    }

    /**
     * When build is set to include a external AAR from a File,
     * the classes defined inside the file should be solved.
     */
    @Test
    void testBuild_withAARConfiguration_fromFile() throws IOException {

        // Execute
        TypeSolver createdTypeSolver = typeSolverBuilder
                .withAAR(new File("src/test/resources/aars/support-compat-24.2.0.aar"))
                .build();

        // Assert
        assertIsSolved(createdTypeSolver, "android.support.v4.app.ActivityCompat");
        assertNotSolved(createdTypeSolver, "com.example.a.non.existing.Class");
    }

    /**
     * When build is set to include external source code from a String,
     * the classes defined inside the file should be solved.
     */
    @Test
    void testBuild_withSourceCodeConfiguration_fromString() {

        // Execute
        TypeSolver createdTypeSolver = typeSolverBuilder
                .withSourceCode("src/test/test_sourcecode/javaparser_new_src/javaparser-core")
                .build();

        // Assert
        assertIsSolved(createdTypeSolver, "com.github.javaparser.ast.Node");
        assertNotSolved(createdTypeSolver, "com.example.a.non.existing.Class");
    }

    /**
     * When build is set to include external source code from a Path,
     * the classes defined inside the file should be solved.
     */
    @Test
    void testBuild_withSourceCodeConfiguration_fromPath() {

        // Execute
        TypeSolver createdTypeSolver = typeSolverBuilder
                .withSourceCode(Paths.get("src/test/test_sourcecode/javaparser_new_src/javaparser-core"))
                .build();

        // Assert
        assertIsSolved(createdTypeSolver, "com.github.javaparser.ast.Node");
        assertNotSolved(createdTypeSolver, "com.example.a.non.existing.Class");
    }

    /**
     * When build is set to include external source code from a File,
     * the classes defined inside the file should be solved.
     */
    @Test
    void testBuild_withSourceCodeConfiguration_fromFile() {

        // Execute
        TypeSolver createdTypeSolver = typeSolverBuilder
                .withSourceCode(new File("src/test/test_sourcecode/javaparser_new_src/javaparser-core"))
                .build();

        // Assert
        assertIsSolved(createdTypeSolver, "com.github.javaparser.ast.Node");
        assertNotSolved(createdTypeSolver, "com.example.a.non.existing.Class");
    }

    /**
     * When build is set to include a custom class loader,
     * the classes defined in the class loader should be solved.
     */
    @Test
    void testBuild_withCustomClassLoaderInConfiguration() {

        // Prepare
        ClassLoader classLoader = TypeSolverBuilderTest.class.getClassLoader();

        // Execute
        TypeSolver createdTypeSolver = typeSolverBuilder
                .withClassLoader(classLoader)
                .build();

        // Assert
        assertIsSolved(createdTypeSolver, "com.github.javaparser.symbolsolver.resolution.typesolvers.TypeSolverBuilderTest");
        assertNotSolved(createdTypeSolver, "com.example.a.non.existing.Class");
    }

    // Static helpers

    /**
     * Assert a class can be resolved inside the current type solver.
     *
     * @param typeSolver The type solver to search.
     * @param className The class to find.
     */
    private static void assertIsSolved(TypeSolver typeSolver, String className) {
        assertTrue(typeSolver.hasType(className), String.format("Unable to solve type %s", className));
    }

    /**
     * Assert a class can't be resolved inside the current type solver.
     *
     * @param typeSolver The type solver to search.
     * @param className The class to find.
     */
    private static void assertNotSolved(TypeSolver typeSolver, String className) {
        assertFalse(typeSolver.hasType(className), String.format("This type solver should not be able to solve type %s", className));
    }

}