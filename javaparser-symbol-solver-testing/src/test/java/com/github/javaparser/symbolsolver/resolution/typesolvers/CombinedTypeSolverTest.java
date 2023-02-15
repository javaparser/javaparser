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

package com.github.javaparser.symbolsolver.resolution.typesolvers;

import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.symbolsolver.cache.Cache;
import com.github.javaparser.symbolsolver.cache.InMemoryCache;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionClassDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver.ExceptionHandlers;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;
import org.mockito.Mockito;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.function.Predicate;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

class CombinedTypeSolverTest extends AbstractTypeSolverTest<CombinedTypeSolver> {

    public CombinedTypeSolverTest() {
        super(CombinedTypeSolver::new);
    }

    static List<Object[]> parameters() {
        // Why these classes? NFE is a subclass, IOOBE is a superclass and ISE is a class without children (by default)
        Predicate<Exception> whitelistTestFilter = ExceptionHandlers.getTypeBasedWhitelist(NumberFormatException.class,
                IndexOutOfBoundsException.class, IllegalStateException.class);
        Predicate<Exception> blacklistTestFilter = ExceptionHandlers.getTypeBasedBlacklist(NumberFormatException.class,
                IndexOutOfBoundsException.class, IllegalStateException.class);

        return Arrays.asList(new Object[][] {
                { new RuntimeException(), ExceptionHandlers.IGNORE_ALL, true }, // 0
                { new RuntimeException(), ExceptionHandlers.IGNORE_NONE, false }, // 1

                { new RuntimeException(), whitelistTestFilter, false }, // 2
                { new IllegalStateException(), whitelistTestFilter, true }, // 3

                { new NumberFormatException(), whitelistTestFilter, true }, // 4
                { new IllegalArgumentException(), whitelistTestFilter, false }, // 5

                { new IndexOutOfBoundsException(), whitelistTestFilter, true }, // 6
                { new ArrayIndexOutOfBoundsException(), whitelistTestFilter, true }, // 7

                { new RuntimeException(), blacklistTestFilter, true }, // 8
                { new NullPointerException(), blacklistTestFilter, true }, // 9
                { new IllegalStateException(), blacklistTestFilter, false }, // 10

                { new NumberFormatException(), blacklistTestFilter, false }, // 11
                { new IllegalArgumentException(), blacklistTestFilter, true }, // 12

                { new IndexOutOfBoundsException(), blacklistTestFilter, false }, // 13
                { new ArrayIndexOutOfBoundsException(), blacklistTestFilter, false }, // 14
        });
    }

    @ParameterizedTest
    @MethodSource("parameters")
    void testExceptionFilter(Exception toBeThrownException, Predicate<Exception> filter, boolean expectForward) {
        TypeSolver erroringTypeSolver = mock(TypeSolver.class);
        when(erroringTypeSolver.getSolvedJavaLangObject()).thenReturn(new ReflectionClassDeclaration(Object.class, erroringTypeSolver));
        doThrow(toBeThrownException).when(erroringTypeSolver).tryToSolveType(any(String.class));

        TypeSolver secondaryTypeSolver = mock(TypeSolver.class);
        when(secondaryTypeSolver.getSolvedJavaLangObject()).thenReturn(new ReflectionClassDeclaration(Object.class, secondaryTypeSolver));
        when(secondaryTypeSolver.tryToSolveType(any(String.class)))
                .thenReturn(SymbolReference.unsolved());

        try {
            new CombinedTypeSolver(filter, erroringTypeSolver, secondaryTypeSolver)
                    .tryToSolveType("an uninteresting string");
            assertTrue(expectForward, "Forwarded, but we expected an exception");
        } catch (Exception e) {
            assertFalse(expectForward, "Exception, but we expected forwarding"); // if we expected the error to be
            // forwarded there shouldn't be an
            // exception
        }

        verify(secondaryTypeSolver, times(expectForward ? 1 : 0)).tryToSolveType(any(String.class));
    }

    @Test
    public void testConstructorWithList() {
        List<TypeSolver> typeSolverList = new ArrayList<>();
        typeSolverList.add(new ReflectionTypeSolver());
        CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver(typeSolverList);

        SymbolReference<ResolvedReferenceTypeDeclaration> resolved = combinedTypeSolver.tryToSolveType(Integer.class.getCanonicalName());
        assertTrue(resolved.isSolved());
    }

    @Test
    public void testConstructorWithArray() {
        CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver(
                new ReflectionTypeSolver()
        );

        SymbolReference<ResolvedReferenceTypeDeclaration> resolved = combinedTypeSolver.tryToSolveType(Integer.class.getCanonicalName());
        assertTrue(resolved.isSolved());
    }

    @Test
    void testConstructorWithNullCache_ShouldThrowNPE() {
        List<TypeSolver> childSolvers = Collections.singletonList(
                new ReflectionTypeSolver()
        );
        assertThrows(NullPointerException.class, () ->
                new CombinedTypeSolver(ExceptionHandlers.IGNORE_NONE, childSolvers, null));
    }

    /**
     * 1. Given a fresh combined type solver, a type is searched in cache and since it doesn't
     *    exist, a new entry should be registered.
     *
     * 2. Given a cache with a cached value, that values should be used.
     */
    @Test
    void testCacheIsUsed_WhenTypeIsRequested() {

        List<TypeSolver> childSolvers = Collections.singletonList(
                new ReflectionTypeSolver()
        );
        Cache<String, SymbolReference<ResolvedReferenceTypeDeclaration>> cache = spy(InMemoryCache.create());
        CombinedTypeSolver combinedSolver = new CombinedTypeSolver(ExceptionHandlers.IGNORE_NONE, childSolvers, cache);
        SymbolReference<ResolvedReferenceTypeDeclaration> reference;

        // 1.
        reference = combinedSolver.tryToSolveType("java.lang.String");
        assertTrue(reference.isSolved());

        verify(cache).get("java.lang.String");
        verify(cache).put("java.lang.String", reference);
        verifyNoMoreInteractions(cache);

        // Reset the interaction counter for the mock, keeping the
        // cached data unchanged.
        Mockito.reset((Object) cache);

        // 2.
        reference = combinedSolver.tryToSolveType("java.lang.String");
        assertTrue(reference.isSolved());
        verify(cache).get("java.lang.String");
        verifyNoMoreInteractions(cache);
    }

    /**
     * 1. When a new type solver is registered, the cache should be reset.
     */
    @Test
    void testUserAddsNewTypeSolver_CacheShouldBeReset() {
        List<TypeSolver> childSolvers = Collections.singletonList(
                new ReflectionTypeSolver()
        );
        Cache<String, SymbolReference<ResolvedReferenceTypeDeclaration>> cache = spy(InMemoryCache.create());
        CombinedTypeSolver combinedSolver = new CombinedTypeSolver(ExceptionHandlers.IGNORE_NONE, childSolvers, cache);

        // Try to solve it
        combinedSolver.add(new ReflectionTypeSolver());
        verify(cache).removeAll();
        verifyNoMoreInteractions(cache);
    }

}
