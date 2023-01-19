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
import org.checkerframework.checker.nullness.qual.NonNull;

import java.io.File;
import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import static com.google.common.base.Preconditions.checkNotNull;

/**
 * TypeSolverBuilder was created with the objective of simplifying
 * the process of creating new type solved. Instead of invoking the
 * constructor directly, the user can build it using the builder pattern.
 *
 * <p/>
 *
 * <b>Example 1:</b>
 * Solve JRE types:
 * <br>
 * <pre>
 *     new TypeSolverBuilder()
 *          .withCurrentJRE()
 *          .build()
 * </pre>
 *
 * <p/>
 *
 * <b>Example 2:</b>
 * Solve JRE and types defined in foo.jar:
 * <br>
 * <pre>
 *     new TypeSolverBuilder()
 *          .withCurrentJRE()
 *          .withJAR("foo.jar")
 *          .build()
 * </pre>
 *
 * @author 4everTheOne
 */
public class TypeSolverBuilder {

    private final List<TypeSolver> typeSolvers = new ArrayList<>();

    /**
     * Append a costum type solver to the build.
     *
     * @param typeSolver The type solver to be added.
     *
     * @return the current builder.
     */
    public TypeSolverBuilder with(@NonNull TypeSolver typeSolver) {
        checkNotNull(typeSolver, "The typeSolver can't be null!");

        typeSolvers.add(typeSolver);
        return this;
    }

    // Builders for Reflection

    /**
     * Allow the type solver to resolve types that are
     * defined in the current Java Runtime Environment (JRE).
     * <p/>
     * Some examples of those types are:
     *
     * <ul>
     *     <li>java.lang.Object</li>
     *     <li>java.lang.String</li>
     *     <li>java.lang.Math</li>
     *     <li>...</li>
     * </ul>
     *
     * @return the current builder.
     *
     * @see ReflectionTypeSolver
     */
    public TypeSolverBuilder withCurrentJRE() {
        TypeSolver javaRuntime = new ReflectionTypeSolver();
        return with(javaRuntime);
    }

    /**
     * Allow the type solver to resolve types that are
     * defined in the current {@link ClassLoader}.
     * <p/>
     * Some examples of those types are:
     *
     * <ul>
     *     <li>java.lang.Object</li>
     *     <li>java.lang.String</li>
     *     <li>java.lang.Math</li>
     *     <li>com.github.javaparser.ast.Node</li>
     *     <li>com.github.javaparser.symbolsolver.resolution.typesolvers.TypeSolverBuilder</li>
     *     <li>...</li>
     * </ul>
     *
     * @return the current builder.
     *
     * @see ReflectionTypeSolver
     */
    public TypeSolverBuilder withCurrentClassloader() {
        TypeSolver classLoaderTypeSolver = new ReflectionTypeSolver(false);
        return with(classLoaderTypeSolver);
    }

    // Builders for JARS

    /**
     * Allow the type solver to resolve types that are
     * defined in a JAR file.
     *
     * @param pathToJar The path to the jar file.
     *
     * @return the current builder.
     *
     * @throws IOException If an I/O exception occurs while reading the Jar.
     *
     * @see JarTypeSolver
     */
    public TypeSolverBuilder withJAR(@NonNull Path pathToJar) throws IOException {
        TypeSolver jarTypeSolver = new JarTypeSolver(pathToJar);
        return with(jarTypeSolver);
    }

    /**
     * Allow the type solver to resolve types that are
     * defined in a JAR file.
     *
     * @param pathToJar The jar file.
     *
     * @return the current builder.
     *
     * @throws IOException If an I/O exception occurs while reading the Jar.
     *
     * @see JarTypeSolver
     */
    public TypeSolverBuilder withJAR(@NonNull File pathToJar) throws IOException {
        TypeSolver jarTypeSolver = new JarTypeSolver(pathToJar);
        return with(jarTypeSolver);
    }

    /**
     * Allow the type solver to resolve types that are
     * defined in a JAR file.
     *
     * @param pathToJar The path to the jar file.
     *
     * @return the current builder.
     *
     * @throws IOException If an I/O exception occurs while reading the Jar.
     *
     * @see JarTypeSolver
     */
    public TypeSolverBuilder withJAR(@NonNull String pathToJar) throws IOException {
        TypeSolver jarTypeSolver = new JarTypeSolver(pathToJar);
        return with(jarTypeSolver);
    }

    // Builders for AarTypeSolver

    /**
     * Allow the type solver to resolve types that are
     * defined in a AAR file.
     *
     * @param pathToAar The path to the AAR file.
     *
     * @return the current builder.
     *
     * @throws IOException If an I/O exception occurs while reading the AAR.
     *
     * @see AarTypeSolver
     */
    public TypeSolverBuilder withAAR(@NonNull Path pathToAar) throws IOException {
        TypeSolver aarTypeSolver = new AarTypeSolver(pathToAar);
        return with(aarTypeSolver);
    }

    /**
     * Allow the type solver to resolve types that are
     * defined in a AAR file.
     *
     * @param pathToAar The AAR file.
     *
     * @return the current builder.
     *
     * @throws IOException If an I/O exception occurs while reading the AAR.
     *
     * @see AarTypeSolver
     */
    public TypeSolverBuilder withAAR(@NonNull File pathToAar) throws IOException {
        TypeSolver aarTypeSolver = new AarTypeSolver(pathToAar);
        return with(aarTypeSolver);
    }

    /**
     * Allow the type solver to resolve types that are
     * defined in a AAR file.
     *
     * @param pathToAar The path to the AAR file.
     *
     * @return the current builder.
     *
     * @throws IOException If an I/O exception occurs while reading the AAR.
     *
     * @see AarTypeSolver
     */
    public TypeSolverBuilder withAAR(@NonNull String pathToAar) throws IOException {
        TypeSolver aarTypeSolver = new AarTypeSolver(pathToAar);
        return with(aarTypeSolver);
    }

    // Builders for JavaParserTypeSolver

    /**
     * Allow the type solver to resolve types using
     * external source code.
     *
     * @param pathToSourceCode The path to the source code.
     *
     * @return the current builder.
     *
     * @see JavaParserTypeSolver
     */
    public TypeSolverBuilder withSourceCode(@NonNull Path pathToSourceCode) {
        TypeSolver aarTypeSolver = new JavaParserTypeSolver(pathToSourceCode);
        return with(aarTypeSolver);
    }

    /**
     * Allow the type solver to resolve types using
     * external source code.
     *
     * @param pathToSourceCode The source code file.
     *
     * @return the current builder.
     *
     * @see JavaParserTypeSolver
     */
    public TypeSolverBuilder withSourceCode(@NonNull File pathToSourceCode) {
        TypeSolver aarTypeSolver = new JavaParserTypeSolver(pathToSourceCode);
        return with(aarTypeSolver);
    }

    /**
     * Allow the type solver to resolve types using
     * external source code.
     *
     * @param pathToSourceCode The path to the source code.
     *
     * @return the current builder.
     *
     * @see JavaParserTypeSolver
     */
    public TypeSolverBuilder withSourceCode(@NonNull String pathToSourceCode) {
        TypeSolver aarTypeSolver = new JavaParserTypeSolver(pathToSourceCode);
        return with(aarTypeSolver);
    }

    // Builders for ClassLoaderTypeSolver

    /**
     * Allow the type solver to resolve types using
     * the provided {@link ClassLoader}.
     *
     * @param classLoader The class loader to be registered.
     *
     * @return the current builder.
     *
     * @see ClassLoaderTypeSolver
     */
    public TypeSolverBuilder withClassLoader(@NonNull ClassLoader classLoader) {
        TypeSolver classLoaderTypeSolver = new ClassLoaderTypeSolver(classLoader);
        return with(classLoaderTypeSolver);
    }

    // build

    /**
     * Convert the current build into a valid {@link TypeSolver}.
     *
     * @return The type solver with the requested configuration.
     *
     * @throws IllegalStateException if no build configuration is provided.
     */
    public TypeSolver build() {
        int typeSolversCount = typeSolvers.size();

        // Check if at least one solver is present
        if (typeSolversCount == 0) {
            throw new IllegalStateException("At least a type solver is expected.");
        }

        // Check if only one exists
        if (typeSolversCount == 1) {
            return typeSolvers.get(0);
        }

        // Combine all type solver
        return new CombinedTypeSolver(typeSolvers);
    }

}
