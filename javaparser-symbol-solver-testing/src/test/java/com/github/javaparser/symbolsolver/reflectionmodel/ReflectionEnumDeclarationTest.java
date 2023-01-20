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

package com.github.javaparser.symbolsolver.reflectionmodel;

import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.AbstractSymbolResolutionTest;
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
