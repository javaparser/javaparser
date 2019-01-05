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

package com.github.javaparser.symbolsolver.reflectionmodel;

import com.github.javaparser.symbolsolver.AbstractSymbolResolutionTest;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import java.util.Collections;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

enum MyModifier {

}

class ReflectionEnumDeclarationTest extends AbstractSymbolResolutionTest {

    private TypeSolver typeSolver = new ReflectionTypeSolver(false);



    ///
    /// Test misc
    ///

    @Test
    void testIsClass() {
        ReflectionEnumDeclaration modifier = (ReflectionEnumDeclaration) typeSolver.solveType("com.github.javaparser.symbolsolver.reflectionmodel.MyModifier");
        assertEquals(false, modifier.isClass());
    }

    @Test
    void testIsInterface() {
        ReflectionEnumDeclaration modifier = (ReflectionEnumDeclaration) typeSolver.solveType("com.github.javaparser.symbolsolver.reflectionmodel.MyModifier");
        assertEquals(false, modifier.isInterface());
    }

    @Test
    void testIsEnum() {
        ReflectionEnumDeclaration modifier = (ReflectionEnumDeclaration) typeSolver.solveType("com.github.javaparser.symbolsolver.reflectionmodel.MyModifier");
        assertEquals(true, modifier.isEnum());
    }

    @Test
    void testIsTypeVariable() {
        ReflectionEnumDeclaration modifier = (ReflectionEnumDeclaration) typeSolver.solveType("com.github.javaparser.symbolsolver.reflectionmodel.MyModifier");
        assertEquals(false, modifier.isTypeParameter());
    }

    @Test
    void testIsType() {
        ReflectionEnumDeclaration modifier = (ReflectionEnumDeclaration) typeSolver.solveType("com.github.javaparser.symbolsolver.reflectionmodel.MyModifier");
        assertEquals(true, modifier.isType());
    }

    @Test
    void testAsType() {
        ReflectionEnumDeclaration modifier = (ReflectionEnumDeclaration) typeSolver.solveType("com.github.javaparser.symbolsolver.reflectionmodel.MyModifier");
        assertEquals(modifier, modifier.asType());
    }

    @Test
    void testAsClass() {
        assertThrows(UnsupportedOperationException.class, () -> {
            ReflectionEnumDeclaration modifier = (ReflectionEnumDeclaration) typeSolver.solveType("com.github.javaparser.symbolsolver.reflectionmodel.MyModifier");
        modifier.asClass();
    });
}

    @Test
    void testAsInterface() {
        assertThrows(UnsupportedOperationException.class, () -> {
            ReflectionEnumDeclaration modifier = (ReflectionEnumDeclaration) typeSolver.solveType("com.github.javaparser.symbolsolver.reflectionmodel.MyModifier");
        modifier.asInterface();
    });
}

    @Test
    void testAsEnum() {
        ReflectionEnumDeclaration modifier = (ReflectionEnumDeclaration) typeSolver.solveType("com.github.javaparser.symbolsolver.reflectionmodel.MyModifier");
        assertEquals(modifier, modifier.asEnum());
    }

    @Test
    void testGetPackageName() {
        ReflectionEnumDeclaration modifier = (ReflectionEnumDeclaration) typeSolver.solveType("com.github.javaparser.symbolsolver.reflectionmodel.MyModifier");
        assertEquals("com.github.javaparser.symbolsolver.reflectionmodel", modifier.getPackageName());
    }

    @Test
    void testGetClassName() {
        ReflectionEnumDeclaration modifier = (ReflectionEnumDeclaration) typeSolver.solveType("com.github.javaparser.symbolsolver.reflectionmodel.MyModifier");
        assertEquals("MyModifier", modifier.getClassName());
    }

    @Test
    void testGetQualifiedName() {
        ReflectionEnumDeclaration modifier = (ReflectionEnumDeclaration) typeSolver.solveType("com.github.javaparser.symbolsolver.reflectionmodel.MyModifier");
        assertEquals("com.github.javaparser.symbolsolver.reflectionmodel.MyModifier", modifier.getQualifiedName());
    }

    @Test
    void testInternalTypesEmpty() {
        ReflectionEnumDeclaration modifier = (ReflectionEnumDeclaration) typeSolver.solveType("com.github.javaparser.symbolsolver.reflectionmodel.MyModifier");
        assertEquals(Collections.emptySet(), modifier.internalTypes());
    }

}
