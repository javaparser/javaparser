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

package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.symbolsolver.AbstractSymbolResolutionTest;
import com.github.javaparser.symbolsolver.javassistmodel.JavassistClassDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JarTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.*;

class SymbolSolverWithJavassistClassTest extends AbstractSymbolResolutionTest {
    private TypeSolver typeSolver;
    private SymbolSolver symbolSolver;
    private JavassistClassDeclaration classDeclarationConcreteClass;
    private JavassistClassDeclaration classDeclarationSubClassOwnJar;
    private JavassistClassDeclaration classDeclarationInterfaceUserOwnJar;
    private JavassistClassDeclaration classDeclarationSubClassIncludedJar;
    private JavassistClassDeclaration classDeclarationInterfaceUserIncludedJar;
    private JavassistClassDeclaration classDeclarationSubClassExcludedJar;
    private JavassistClassDeclaration classDeclarationInterfaceUserExcludedJar;

    @BeforeEach
    void setup() throws IOException {
        final Path pathToMainJar = adaptPath("src/test/resources/javassist_symbols/main_jar/main_jar.jar");
        final Path pathToIncludedJar = adaptPath("src/test/resources/javassist_symbols/included_jar/included_jar.jar");
        typeSolver = new CombinedTypeSolver(new JarTypeSolver(pathToIncludedJar), new JarTypeSolver(pathToMainJar), new ReflectionTypeSolver());

        symbolSolver = new SymbolSolver(typeSolver);

        classDeclarationConcreteClass = (JavassistClassDeclaration) typeSolver.solveType("com.github.javaparser.javasymbolsolver.javassist_symbols.main_jar.ConcreteClass");
        classDeclarationSubClassOwnJar = (JavassistClassDeclaration) typeSolver.solveType("com.github.javaparser.javasymbolsolver.javassist_symbols.main_jar.SubClassOwnJar");
        classDeclarationSubClassIncludedJar = (JavassistClassDeclaration) typeSolver.solveType("com.github.javaparser.javasymbolsolver.javassist_symbols.main_jar.SubClassIncludedJar");
        classDeclarationSubClassExcludedJar = (JavassistClassDeclaration) typeSolver.solveType("com.github.javaparser.javasymbolsolver.javassist_symbols.main_jar.SubClassExcludedJar");
        classDeclarationInterfaceUserOwnJar = (JavassistClassDeclaration) typeSolver.solveType("com.github.javaparser.javasymbolsolver.javassist_symbols.main_jar.InterfaceUserOwnJar");
        classDeclarationInterfaceUserIncludedJar = (JavassistClassDeclaration) typeSolver.solveType("com.github.javaparser.javasymbolsolver.javassist_symbols.main_jar.InterfaceUserIncludedJar");
        classDeclarationInterfaceUserExcludedJar = (JavassistClassDeclaration) typeSolver.solveType("com.github.javaparser.javasymbolsolver.javassist_symbols.main_jar.InterfaceUserExcludedJar");
    }

    @Test
    void testSolveSymbolInTypeCanSolveFirstOwnField() {
        assertCanSolveSymbol("STATIC_STRING", classDeclarationConcreteClass);
    }

    @Test
    void testSolveSymbolInTypeCanSolveSecondOwnField() {
        assertCanSolveSymbol("SECOND_STRING", classDeclarationConcreteClass);
    }

    @Test
    void testSolveSymbolInTypeCantResolveNonExistentField() {
        SymbolReference<? extends ResolvedValueDeclaration> solvedSymbol = symbolSolver.solveSymbolInType(classDeclarationConcreteClass, "FIELD_THAT_DOES_NOT_EXIST");

        assertFalse(solvedSymbol.isSolved());

        try {
            solvedSymbol.getCorrespondingDeclaration();
        } catch (Exception e) {
            assertTrue(e instanceof UnsupportedOperationException);
            assertEquals("CorrespondingDeclaration not available for unsolved symbol.", e.getMessage());
            return;
        }
        fail("Expected UnsupportedOperationException when requesting CorrespondingDeclaration on unsolved SymbolRefernce");
    }

    @Test
    void testSolveSymbolInTypeCanResolveFieldInSuper() {
        assertCanSolveSymbol("SUPER_FIELD", classDeclarationSubClassOwnJar);
    }

    @Test
    void testSolveSymbolInTypeCanResolveFieldInSuperIncludedJar() {
        assertCanSolveSymbol("SUPER_FIELD", classDeclarationSubClassIncludedJar);
    }

    @Test
    void testSolveSymbolInTypeThrowsExceptionOnResolveFieldInSuperExcludedJar() {
        try {
            symbolSolver.solveSymbolInType(classDeclarationSubClassExcludedJar, "SUPER_FIELD");
        } catch (Exception e) {
            assertTrue(e instanceof UnsolvedSymbolException);
            assertEquals("Unsolved symbol : com.github.javaparser.javasymbolsolver.javassist_symbols.excluded_jar.SuperClassExcludedJar", e.getMessage());
            return;
        }
        fail("Excepted NotFoundException wrapped in a RuntimeException, but got no exception.");
    }

    @Test
    void testSolveSymbolInTypeCanResolveFieldInInterface() {
        assertCanSolveSymbol("INTERFACE_FIELD", classDeclarationInterfaceUserOwnJar);
    }

    @Test
    void testSolveSymbolInTypeCanResolveFieldInInterfaceIncludedJar() {
        assertCanSolveSymbol("INTERFACE_FIELD", classDeclarationInterfaceUserIncludedJar);
    }

    @Test
    void testSolveSymbolInTypeThrowsExceptionOnResolveFieldInInterfaceExcludedJar() {
        try {
            symbolSolver.solveSymbolInType(classDeclarationInterfaceUserExcludedJar, "INTERFACE_FIELD");
        } catch (Exception e) {
            assertTrue(e instanceof UnsolvedSymbolException);
            assertEquals("Unsolved symbol : com.github.javaparser.javasymbolsolver.javassist_symbols.excluded_jar.InterfaceExcludedJar", e.getMessage());
            return;
        }
        fail("Excepted NotFoundException wrapped in a RuntimeException, but got no exception.");
    }

    private void assertCanSolveSymbol(String symbolName, JavassistClassDeclaration classDeclaration) {
        SymbolReference<? extends ResolvedValueDeclaration> solvedSymbol = symbolSolver.solveSymbolInType(classDeclaration, symbolName);

        assertTrue(solvedSymbol.isSolved());
        assertEquals(symbolName, solvedSymbol.getCorrespondingDeclaration().asField().getName());
    }
}
