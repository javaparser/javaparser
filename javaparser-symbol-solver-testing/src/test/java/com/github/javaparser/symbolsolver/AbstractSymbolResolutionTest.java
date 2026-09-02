/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2026 The JavaParser Team.
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

package com.github.javaparser.symbolsolver;

import com.github.javaparser.resolution.SymbolResolver;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.github.javaparser.utils.CodeGenerationUtils;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import org.junit.jupiter.api.AfterAll;

public abstract class AbstractSymbolResolutionTest {

    // StaticJavaParser is now reset before/after every test in this module by
    // StaticJavaParserConfigResetExtension (auto-detected via
    // src/test/resources/META-INF/services), so this class no longer needs its
    // own @BeforeEach/@AfterEach reset. See that class for the full explanation
    // of the @BeforeAll incompatibility this reset creates.

    @AfterAll
    public static void tearDown() {
        // clear internal caches
        JavaParserFacade.clearInstances();
    }

    /**
     * Whether the running JRE exposes {@code java.util.SequencedCollection} (JDK 21+).
     */
    protected static boolean hasSequencedCollection() {
        try {
            Class.forName("java.util.SequencedCollection");
            return true;
        } catch (ClassNotFoundException e) {
            return false;
        }
    }

    /**
     * Whether {@code Object.wait0(long)} is present (JDK 21 split of {@code wait(long)}).
     */
    protected static boolean hasWait0() {
        try {
            Object.class.getDeclaredMethod("wait0", long.class);
            return true;
        } catch (NoSuchMethodException e) {
            return false;
        }
    }

    /**
     * Whether {@code Object.registerNatives()} is present (removed in JDK 14).
     */
    protected static boolean hasRegisterNatives() {
        try {
            Object.class.getDeclaredMethod("registerNatives");
            return true;
        } catch (NoSuchMethodException e) {
            return false;
        }
    }

    /**
     * Whether {@code java.lang.constant.Constable} is present (JDK 12+).
     */
    protected static boolean hasConstable() {
        try {
            Class.forName("java.lang.constant.Constable");
            return true;
        } catch (ClassNotFoundException e) {
            return false;
        }
    }

    protected static Path adaptPath(Path path) {
        if (Files.exists(path)) {
            return path.toAbsolutePath();
        }
        Path underSymbolSolver = CodeGenerationUtils.mavenModuleRoot(AbstractSymbolResolutionTest.class)
                .resolve("javaparser-symbol-solver-testing")
                .resolve(path);
        if (Files.exists(underSymbolSolver)) {
            return underSymbolSolver;
        } else {
            throw new IllegalArgumentException("I cannot adapt the path " + path);
        }
    }

    protected static Path adaptPath(String path) {
        return adaptPath(Paths.get(path));
    }

    protected SymbolResolver symbolResolver(TypeSolver typeSolver) {
        return new JavaSymbolSolver(typeSolver);
    }

    protected TypeSolver defaultTypeSolver() {
        return new ReflectionTypeSolver();
    }
}
