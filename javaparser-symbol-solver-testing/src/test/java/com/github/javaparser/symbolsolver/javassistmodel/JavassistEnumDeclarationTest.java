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

package com.github.javaparser.symbolsolver.javassistmodel;

import com.github.javaparser.resolution.declarations.ResolvedEnumDeclaration;
import com.github.javaparser.symbolsolver.AbstractSymbolResolutionTest;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JarTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.assertThrows;

class JavassistEnumDeclarationTest extends AbstractSymbolResolutionTest {

    private TypeSolver typeSolver;

    private TypeSolver anotherTypeSolver;

    @BeforeEach
    void setup() throws IOException {
        Path pathToJar = adaptPath("src/test/resources/javaparser-core-3.0.0-alpha.2.jar");
        typeSolver = new CombinedTypeSolver(new JarTypeSolver(pathToJar), new ReflectionTypeSolver());

        Path anotherPathToJar = adaptPath("src/test/resources/test-artifact-1.0.0.jar");
        anotherTypeSolver = new CombinedTypeSolver(new JarTypeSolver(anotherPathToJar), new ReflectionTypeSolver());
    }

    ///
    /// Test misc
    ///

    @Test
    void testIsClass() {
        ResolvedEnumDeclaration modifier = (ResolvedEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals(false, modifier.isClass());
    }

    @Test
    void testIsInterface() {
        ResolvedEnumDeclaration modifier = (ResolvedEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals(false, modifier.isInterface());
    }

    @Test
    void testIsEnum() {
        ResolvedEnumDeclaration modifier = (ResolvedEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals(true, modifier.isEnum());
    }

    @Test
    void testIsTypeVariable() {
        ResolvedEnumDeclaration modifier = (ResolvedEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals(false, modifier.isTypeParameter());
    }

    @Test
    void testIsType() {
        ResolvedEnumDeclaration modifier = (ResolvedEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals(true, modifier.isType());
    }

    @Test
    void testAsType() {
        ResolvedEnumDeclaration modifier = (ResolvedEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals(modifier, modifier.asType());
    }

    @Test
    void testAsClass() {
        assertThrows(UnsupportedOperationException.class, () -> {
            ResolvedEnumDeclaration modifier = (ResolvedEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
        modifier.asClass();
    });
}

    @Test
    void testAsInterface() {
        assertThrows(UnsupportedOperationException.class, () -> {
            ResolvedEnumDeclaration modifier = (ResolvedEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
        modifier.asInterface();
    });
}

    @Test
    void testAsEnum() {
        ResolvedEnumDeclaration modifier = (ResolvedEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals(modifier, modifier.asEnum());
    }

    @Test
    void testGetPackageName() {
        ResolvedEnumDeclaration modifier = (ResolvedEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals("com.github.javaparser.ast", modifier.getPackageName());
    }

    @Test
    void testGetClassName() {
        ResolvedEnumDeclaration modifier = (ResolvedEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals("Modifier", modifier.getClassName());
    }

    @Test
    void testGetQualifiedName() {
        ResolvedEnumDeclaration modifier = (ResolvedEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals("com.github.javaparser.ast.Modifier", modifier.getQualifiedName());
    }

    @Test
    void testHasDirectlyAnnotation(){
        ResolvedEnumDeclaration compilationUnit = (ResolvedEnumDeclaration) anotherTypeSolver.solveType("com.github.javaparser.test.TestEnum");
        assertTrue(compilationUnit.hasDirectlyAnnotation("com.github.javaparser.test.TestAnnotation"));
    }

    @Test
    void testHasAnnotation(){
        ResolvedEnumDeclaration compilationUnit = (ResolvedEnumDeclaration) anotherTypeSolver.solveType("com.github.javaparser.test.TestParentEnum");
        assertTrue(compilationUnit.hasAnnotation("com.github.javaparser.test.TestAnnotation"));
    }

    ///
    /// Test ancestors
    ///

}
