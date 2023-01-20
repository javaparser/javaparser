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
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionFactory;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class MemoryTypeSolverTest extends AbstractTypeSolverTest<MemoryTypeSolver> {

    public MemoryTypeSolverTest() {
        super(MemoryTypeSolver::new);
    }

    /**
     * When solving a type that isn't registered in the memory should fail, while
     * a existing type should be solved.
     */
    @Test
    void solveNonExistentShouldFailAndExistentTypeShouldSolve() {
        Class<String> expectedExistingClass = String.class;
        Class<Integer> expectedNonExistingClass = Integer.class;

        MemoryTypeSolver memoryTypeSolver = createTypeSolver(expectedExistingClass);
        assertFalse(memoryTypeSolver.tryToSolveType(expectedNonExistingClass.getCanonicalName()).isSolved());
        assertTrue(memoryTypeSolver.tryToSolveType(expectedExistingClass.getCanonicalName()).isSolved());
    }

    /**
     * If two instance of the {@link MemoryTypeSolver} have the same information in memory
     * should be considered equals.
     */
    @Test
    void memoryTypeSolversAreEqualsIfMemoryInformationMatches() {
        MemoryTypeSolver solver1 = createTypeSolver();
        MemoryTypeSolver solver2 = createTypeSolver();
        assertEquals(solver1, solver2);

        registerClassInMemory(solver1, String.class);
        assertNotEquals(solver1, solver2);

        registerClassInMemory(solver2, String.class);
        assertEquals(solver1, solver2);
    }

    /**
     * If two instance of the {@link MemoryTypeSolver} have the same information in memory
     * should has the same hashcode.
     */
    @Test
    void memoryTypeSolversHaveSameHashCodeIfMemoryInformationMatches() {
        MemoryTypeSolver solver1 = createTypeSolver();
        MemoryTypeSolver solver2 = createTypeSolver();
        assertEquals(solver1.hashCode(), solver2.hashCode());

        registerClassInMemory(solver1, String.class);
        assertNotEquals(solver1.hashCode(), solver2.hashCode());

        registerClassInMemory(solver2, String.class);
        assertEquals(solver1.hashCode(), solver2.hashCode());
    }

    /**
     * Create the type solver with pre-registered classes.
     *
     * @param multipleClazz The classes to be registered.
     *
     * @return The created memory solver.
     */
    public MemoryTypeSolver createTypeSolver(Class<?>... multipleClazz) {
        MemoryTypeSolver memorySolver = super.createTypeSolver();

        for (Class<?> clazz : multipleClazz) {
            registerClassInMemory(memorySolver, clazz);
        }

        return memorySolver;
    }

    /**
     * Register the class in memory.
     *
     * @param memorySolver  The memory solver where the information should be registered.
     * @param clazz         The class to be registered.
     */
    private static void registerClassInMemory(MemoryTypeSolver memorySolver, Class<?> clazz) {
        ResolvedReferenceTypeDeclaration declaration = ReflectionFactory.typeDeclarationFor(clazz, memorySolver);
        memorySolver.addDeclaration(clazz.getCanonicalName(), declaration);
    }

}
