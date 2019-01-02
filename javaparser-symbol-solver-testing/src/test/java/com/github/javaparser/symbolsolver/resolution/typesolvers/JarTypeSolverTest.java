/*
 * Copyright 2016 Federico Tomassetti
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.github.javaparser.symbolsolver.resolution.typesolvers;

import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.symbolsolver.AbstractSymbolResolutionTest;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Path;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;


class JarTypeSolverTest extends AbstractSymbolResolutionTest {

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

}
