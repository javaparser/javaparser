/*
 * Copyright (C) 2013-2023 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.model.resolution;

import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedClassDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedParameterDeclaration;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionClassDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class SymbolReferenceTest {

    private final TypeSolver typeSolver = new ReflectionTypeSolver();

    @Test
    void testResolvedSymbol() {
        ResolvedDeclaration resolvedDeclaration = new ReflectionClassDeclaration(String.class, typeSolver);
        SymbolReference<ResolvedDeclaration> symbol = SymbolReference.solved(resolvedDeclaration);

        assertNotNull(symbol);
        assertNotNull(symbol.getDeclaration());
        assertTrue(symbol.getDeclaration().isPresent());
    }

    @Test
    void testUnresolvedSymbol() {
        SymbolReference<ResolvedDeclaration> symbol = SymbolReference.unsolved();

        assertNotNull(symbol);
        assertNotNull(symbol.getDeclaration());
        assertFalse(symbol.getDeclaration().isPresent());
    }

    @Test
    void testAdaptSymbolForSubClass() {
        ResolvedDeclaration resolvedDeclaration = new ReflectionClassDeclaration(String.class, typeSolver);
        SymbolReference<ResolvedDeclaration> symbol = SymbolReference.solved(resolvedDeclaration);
        SymbolReference<ResolvedClassDeclaration> adaptedSymbol = SymbolReference.adapt(symbol, ResolvedClassDeclaration.class);

        assertNotNull(adaptedSymbol);
        assertNotNull(adaptedSymbol.getDeclaration());
        assertTrue(adaptedSymbol.getDeclaration().isPresent());
    }

    @Test
    void testAdaptSymbolForInvalidSubClass() {
        ResolvedClassDeclaration resolvedDeclaration = new ReflectionClassDeclaration(String.class, typeSolver);
        SymbolReference<ResolvedClassDeclaration> symbol = SymbolReference.solved(resolvedDeclaration);
        SymbolReference<ResolvedParameterDeclaration> adaptedSymbol = SymbolReference.adapt(symbol, ResolvedParameterDeclaration.class);

        assertNotNull(adaptedSymbol);
        assertNotNull(adaptedSymbol.getDeclaration());
        assertFalse(adaptedSymbol.getDeclaration().isPresent());
    }

    @Test
    void testAdaptSymbolForSuperClass() {
        ResolvedClassDeclaration resolvedDeclaration = new ReflectionClassDeclaration(String.class, typeSolver);
        SymbolReference<ResolvedClassDeclaration> symbol = SymbolReference.solved(resolvedDeclaration);
        SymbolReference<ResolvedDeclaration> adaptedSymbol = SymbolReference.adapt(symbol, ResolvedDeclaration.class);

        assertNotNull(adaptedSymbol);
        assertNotNull(adaptedSymbol.getDeclaration());
        assertTrue(adaptedSymbol.getDeclaration().isPresent());
    }

    @Test
    void testIsSolvedWithResolvedSymbol() {
        ResolvedClassDeclaration resolvedDeclaration = new ReflectionClassDeclaration(String.class, typeSolver);
        SymbolReference<ResolvedClassDeclaration> symbol = SymbolReference.solved(resolvedDeclaration);

        assertNotNull(symbol);
        assertTrue(symbol.isSolved());
        assertEquals(resolvedDeclaration, symbol.getCorrespondingDeclaration());
    }

    @Test
    void testIsSolvedWithUnresolvedSymbol() {
        SymbolReference<ResolvedClassDeclaration> symbol = SymbolReference.unsolved();

        assertNotNull(symbol);
        assertFalse(symbol.isSolved());
        assertThrows(UnsupportedOperationException.class, symbol::getCorrespondingDeclaration);
    }

}