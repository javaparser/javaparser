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

package com.github.javaparser.symbolsolver.resolution.typesolvers;

import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.model.SymbolReference;
import org.junit.jupiter.api.Test;

import java.util.Map;
import java.util.function.Supplier;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

abstract class ClassLoaderTypeSolverTest<T extends ClassLoaderTypeSolver> extends AbstractTypeSolverTest<T> {

    public ClassLoaderTypeSolverTest(Supplier<T> solverSupplier) {
        super(solverSupplier);
    }

    /**
     * When solving a nested type the argument may be a nested class but not in a canonical format.
     * This test checks when name is supplied without the canonical name the solver still resolves.
     */
    @Test
    void solveNonCanonicalNameForNestedClass() {
        String expectedCanonicalName = Map.Entry.class.getCanonicalName();
        String suppliedName = "java.util.Map.Entry";

        T typeSolver = createTypeSolver();
        SymbolReference<ResolvedReferenceTypeDeclaration> solvedType = typeSolver.tryToSolveType(suppliedName);
        assertTrue(solvedType.isSolved());

        ResolvedReferenceTypeDeclaration resolvedDeclaration = solvedType.getCorrespondingDeclaration();
        assertEquals(expectedCanonicalName, resolvedDeclaration.getQualifiedName());
    }

}
