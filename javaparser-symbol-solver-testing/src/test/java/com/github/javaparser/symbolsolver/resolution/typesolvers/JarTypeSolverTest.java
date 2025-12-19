/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2024 The JavaParser Team.
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

import static org.junit.jupiter.api.Assertions.*;

import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.google.common.collect.Sets;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.function.Supplier;
import java.util.jar.JarEntry;
import java.util.jar.JarInputStream;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

class JarTypeSolverTest extends AbstractTypeSolverTest<JarTypeSolver> {

    private static final Supplier<JarTypeSolver> JAR_TYPE_PROVIDER = () -> {
        try {
            Path pathToJar = adaptPath("src/test/resources/javaparser-core-2.1.0.jar");
            return new JarTypeSolver(pathToJar);
        } catch (IOException e) {
            throw new RuntimeException("Unable to create the JarTypeSolver.", e);
        }
    };

    public JarTypeSolverTest() {
        super(JAR_TYPE_PROVIDER);
    }

    @Test
    void initial() throws IOException {
        Path pathToJar = adaptPath("src/test/resources/javaparser-core-2.1.0.jar");
        JarTypeSolver jarTypeSolver = new JarTypeSolver(pathToJar);
        assertEquals(
                true,
                jarTypeSolver
                        .tryToSolveType("com.github.javaparser.SourcesHelper")
                        .isSolved());
        assertEquals(
                true,
                jarTypeSolver.tryToSolveType("com.github.javaparser.Token").isSolved());
        assertEquals(
                true,
                jarTypeSolver
                        .tryToSolveType("com.github.javaparser.ASTParser.JJCalls")
                        .isSolved());
        assertEquals(
                false,
                jarTypeSolver
                        .tryToSolveType("com.github.javaparser.ASTParser.Foo")
                        .isSolved());
        assertEquals(
                false, jarTypeSolver.tryToSolveType("com.github.javaparser.Foo").isSolved());
        assertEquals(false, jarTypeSolver.tryToSolveType("Foo").isSolved());
    }

    @Test
    void classFileHierarchy(@TempDir Path tempDir) throws IOException {
        Path pathToJar = adaptPath("src/test/resources/javaparser-core-2.1.0.jar");

        // Unpack the jar file into a class hierarchy
        try (JarInputStream jarInputStream = new JarInputStream(Files.newInputStream(pathToJar))) {
            for (JarEntry entry = jarInputStream.getNextJarEntry();
                    entry != null;
                    entry = jarInputStream.getNextJarEntry()) {
                if (entry.isDirectory()) {
                    Files.createDirectories(tempDir.resolve(entry.getName()));
                } else {
                    Files.copy(jarInputStream, tempDir.resolve(entry.getName()));
                }
            }
        }

        JarTypeSolver jarTypeSolver = new JarTypeSolver(tempDir);
        assertEquals(
                true,
                jarTypeSolver
                        .tryToSolveType("com.github.javaparser.SourcesHelper")
                        .isSolved());
        assertEquals(
                false, jarTypeSolver.tryToSolveType("com.github.javaparser.Foo").isSolved());
    }

    @Test
    void dependenciesBetweenJarsNotTriggeringReferences() throws IOException {
        Path pathToJar1 = adaptPath("src/test/resources/jar1.jar");
        JarTypeSolver jarTypeSolver1 = new JarTypeSolver(pathToJar1);
        assertEquals(true, jarTypeSolver1.tryToSolveType("foo.bar.A").isSolved());

        Path pathToJar2 = adaptPath("src/test/resources/jar2.jar");
        JarTypeSolver jarTypeSolver2 = new JarTypeSolver(pathToJar2);
        assertEquals(true, jarTypeSolver2.tryToSolveType("foo.zum.B").isSolved());
    }

    @Test
    void dependenciesBetweenJarsTriggeringReferencesThatCannotBeResolved() throws IOException {
        assertThrows(UnsolvedSymbolException.class, () -> {
            Path pathToJar2 = adaptPath("src/test/resources/jar2.jar");
            JarTypeSolver jarTypeSolver2 = new JarTypeSolver(pathToJar2);
            ResolvedReferenceTypeDeclaration b =
                    jarTypeSolver2.tryToSolveType("foo.zum.B").getCorrespondingDeclaration();
            b.getAncestors();
        });
    }

    @Test
    void dependenciesBetweenJarsTriggeringReferencesThatCanBeResolved() throws IOException {
        Path pathToJar1 = adaptPath("src/test/resources/jar1.jar");
        JarTypeSolver jarTypeSolver1 = new JarTypeSolver(pathToJar1);

        Path pathToJar2 = adaptPath("src/test/resources/jar2.jar");
        JarTypeSolver jarTypeSolver2 = new JarTypeSolver(pathToJar2);

        CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver(jarTypeSolver1, jarTypeSolver2);

        ResolvedReferenceTypeDeclaration b =
                combinedTypeSolver.tryToSolveType("foo.zum.B").getCorrespondingDeclaration();
        List<ResolvedReferenceType> ancestors = b.getAncestors();
        assertEquals(1, ancestors.size());
    }

    /**
     * The {@link JarTypeSolver} should not solve the JRE types. If we want to solve the JRE types
     * we should combine it with a {@link ReflectionTypeSolver}.
     *
     * @throws IOException If an I/O exception occur.
     */
    @Test
    void whenJarTypeSolverShouldNotSolveJREType() throws IOException {
        Path pathToJar = adaptPath("src/test/resources/javaparser-core-2.1.0.jar");
        JarTypeSolver typeSolver = new JarTypeSolver(pathToJar);
        assertFalse(typeSolver.tryToSolveType("java.lang.Object").isSolved());
    }

    @Test
    void solveTypeShouldReturnTheCorrespondingDeclarationWhenAvailable() throws IOException {
        Path pathToJar = adaptPath("src/test/resources/javaparser-core-2.1.0.jar");
        JarTypeSolver typeSolver = new JarTypeSolver(pathToJar);
        ResolvedReferenceTypeDeclaration nodeType = typeSolver.solveType("com.github.javaparser.ast.Node");
        assertEquals("com.github.javaparser.ast.Node", nodeType.getQualifiedName());
    }

    @Test
    void solveTypeShouldThrowUnsolvedSymbolWhenNotAvailable() throws IOException {
        Path pathToJar = adaptPath("src/test/resources/javaparser-core-2.1.0.jar");
        JarTypeSolver typeSolver = new JarTypeSolver(pathToJar);
        assertThrows(UnsolvedSymbolException.class, () -> typeSolver.solveType("java.lang.Object"));
    }

    @Test
    void createTypeSolverFromInputStream() throws IOException {
        Path pathToJar = adaptPath("src/test/resources/javaparser-core-2.1.0.jar");
        try (FileInputStream fileInputStream = new FileInputStream(pathToJar.toFile())) {
            JarTypeSolver typeSolver = new JarTypeSolver(fileInputStream);
            assertTrue(
                    typeSolver.tryToSolveType("com.github.javaparser.ast.Node").isSolved());
        }
    }

    @Test
    void whenTheJarIsNotFoundShouldThrowAFileNotFoundException(@TempDir Path tempDirectory) {
        Path pathToJar = tempDirectory.resolve("a_non_existing_file.jar");
        assertThrows(FileNotFoundException.class, () -> new JarTypeSolver(pathToJar));
    }

    @Test
    void theJarTypeShouldCacheTheListOfKnownTypes() throws IOException {
        String typeA = "foo.bar.A";
        String typeB = "foo.zum.B";

        Path pathToJar1 = adaptPath("src/test/resources/jar1.jar");
        JarTypeSolver jarTypeSolver1 = new JarTypeSolver(pathToJar1);
        assertEquals(Sets.newHashSet(typeA), jarTypeSolver1.getKnownClasses());
        assertTrue(jarTypeSolver1.tryToSolveType(typeA).isSolved());
        assertFalse(jarTypeSolver1.tryToSolveType(typeB).isSolved());

        Path pathToJar2 = adaptPath("src/test/resources/jar2.jar");
        JarTypeSolver jarTypeSolver2 = new JarTypeSolver(pathToJar2);
        assertEquals(Sets.newHashSet(typeB), jarTypeSolver2.getKnownClasses());
        assertTrue(jarTypeSolver2.tryToSolveType(typeB).isSolved());
        assertFalse(jarTypeSolver2.tryToSolveType(typeA).isSolved());
    }
}
