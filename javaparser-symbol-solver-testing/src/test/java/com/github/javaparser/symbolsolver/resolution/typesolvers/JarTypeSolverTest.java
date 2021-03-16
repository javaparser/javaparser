/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2019 The JavaParser Team.
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

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

import java.io.IOException;
import java.nio.file.Path;
import java.util.List;
import java.util.function.Supplier;

import org.junit.jupiter.api.Test;

import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.types.ResolvedReferenceType;


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
        assertEquals(true, jarTypeSolver.tryToSolveType("com.github.javaparser.SourcesHelper").isSolved());
        assertEquals(true, jarTypeSolver.tryToSolveType("com.github.javaparser.Token").isSolved());
        assertEquals(true, jarTypeSolver.tryToSolveType("com.github.javaparser.ASTParser.JJCalls").isSolved());
        assertEquals(false, jarTypeSolver.tryToSolveType("com.github.javaparser.ASTParser.Foo").isSolved());
        assertEquals(false, jarTypeSolver.tryToSolveType("com.github.javaparser.Foo").isSolved());
        assertEquals(false, jarTypeSolver.tryToSolveType("Foo").isSolved());
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
        ResolvedReferenceTypeDeclaration b = jarTypeSolver2.tryToSolveType("foo.zum.B").getCorrespondingDeclaration();
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

        ResolvedReferenceTypeDeclaration b = combinedTypeSolver.tryToSolveType("foo.zum.B").getCorrespondingDeclaration();
        List<ResolvedReferenceType> ancestors = b.getAncestors();
        assertEquals(1, ancestors.size());
    }
    
    @Test
    void cleanUp() throws IOException {
        Path pathToJar = adaptPath("src/test/resources/javaparser-core-2.1.0.jar");
        JarTypeSolver jarTypeSolver = new JarTypeSolver(pathToJar);
        JarTypeSolver.ResourceRegistry.getRegistry().cleanUp();
        jarTypeSolver = new JarTypeSolver(pathToJar);
        assertEquals(true, jarTypeSolver.tryToSolveType("com.github.javaparser.SourcesHelper").isSolved());
    }
    
    @Test
    void cleanUpWithIllegalStateException() throws IOException {
        Path pathToJar = adaptPath("src/test/resources/javaparser-core-2.1.0.jar");
        JarTypeSolver jarTypeSolver = new JarTypeSolver(pathToJar);
        JarTypeSolver.ResourceRegistry.getRegistry().cleanUp();
        assertThrows(IllegalStateException.class, () -> jarTypeSolver.tryToSolveType("com.github.javaparser.SourcesHelper").isSolved());
    }

}
