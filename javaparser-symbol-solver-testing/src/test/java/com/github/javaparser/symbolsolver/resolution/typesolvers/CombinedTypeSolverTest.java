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

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

import java.util.Arrays;
import java.util.List;
import java.util.function.Predicate;

import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver.ExceptionHandlers;

class CombinedTypeSolverTest {

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
        doThrow(toBeThrownException).when(erroringTypeSolver).tryToSolveType(any(String.class));

        TypeSolver secondaryTypeSolver = mock(TypeSolver.class);
        when(secondaryTypeSolver.tryToSolveType(any(String.class)))
                .thenReturn(SymbolReference.unsolved(ResolvedReferenceTypeDeclaration.class));

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

}
