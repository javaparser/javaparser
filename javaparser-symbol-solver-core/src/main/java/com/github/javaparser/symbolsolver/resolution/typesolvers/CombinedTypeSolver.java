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

import java.util.ArrayList;
import java.util.List;
import java.util.function.Predicate;

import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;

/**
 * A container for type solvers. All solving is done by the contained type solvers.
 * This helps you when an API asks for a single type solver, but you need several.
 *
 * @author Federico Tomassetti
 */
public class CombinedTypeSolver implements TypeSolver {

    private TypeSolver parent;
    private List<TypeSolver> elements = new ArrayList<>();
    private Predicate<Exception> errorFilter;

    public CombinedTypeSolver(TypeSolver... elements) {
        this(ExceptionFilters.IGNORE_ALL, elements);
    }

    /** @see #setFilter(Predicate) */
    public CombinedTypeSolver(Predicate<Exception> errorFilter, TypeSolver... elements) {
        setFilter(errorFilter);

        for (TypeSolver el : elements) {
            add(el);
        }
    }

    /**
     * @param errorFilter A filter which determines if an exception raised while solving should be ignored.
     *            Should return <code>true</code> when the exception must be <b>ignored</b>.
     */
    public void setFilter(Predicate<Exception> errorFilter) {
        this.errorFilter = errorFilter;
    }

    @Override
    public TypeSolver getParent() {
        return parent;
    }

    @Override
    public void setParent(TypeSolver parent) {
        this.parent = parent;
    }

    public void add(TypeSolver typeSolver) {
        this.elements.add(typeSolver);
        typeSolver.setParent(this);
    }

    @Override
    public SymbolReference<ResolvedReferenceTypeDeclaration> tryToSolveType(String name) {
        for (TypeSolver ts : elements) {
            try {
                SymbolReference<ResolvedReferenceTypeDeclaration> res = ts.tryToSolveType(name);
                if (res.isSolved()) {
                    return res;
                }
            } catch (Exception e) {
                if (!errorFilter.test(e)) { // we shouldn't ignore this exception
                    throw e;
                }
            }
        }
        return SymbolReference.unsolved(ResolvedReferenceTypeDeclaration.class);
    }

    @Override
    public ResolvedReferenceTypeDeclaration solveType(String name) throws UnsolvedSymbolException {
        SymbolReference<ResolvedReferenceTypeDeclaration> res = tryToSolveType(name);
        if (res.isSolved()) {
            return res.getCorrespondingDeclaration();
        } else {
            throw new UnsolvedSymbolException(name);
        }
    }

    /** Provides some convenience filter implementations */
    public static class ExceptionFilters {

        /** Doesn't ignore any exceptions (default) */
        public static final Predicate<Exception> IGNORE_NONE = e -> false;

        /** Ignores all exceptions */
        public static final Predicate<Exception> IGNORE_ALL = e -> true;

        /**
         * Ignores any exception that is {@link Class#isAssignableFrom(Class) assignable from}
         * {@link UnsupportedOperationException}.
         * 
         * @see #getTypeBasedWhitelist(Class...)
         */
        public static final Predicate<Exception> IGNORE_UNSUPPORTED_OPERATION = getTypeBasedWhitelist(
                UnsupportedOperationException.class);

        /**
         * Ignores any exception that is {@link Class#isAssignableFrom(Class) assignable from}
         * {@link UnsolvedSymbolException}.
         * 
         * @see #getTypeBasedWhitelist(Class...)
         */
        public static final Predicate<Exception> IGNORE_UNSOLVED_SYMBOL = getTypeBasedWhitelist(
                UnsolvedSymbolException.class);

        /**
         * Ignores any exception that is {@link Class#isAssignableFrom(Class) assignable from} either
         * {@link UnsolvedSymbolException} or {@link UnsupportedOperationException}.
         * 
         * @see #IGNORE_UNSOLVED_SYMBOL
         * @see #IGNORE_UNSUPPORTED_OPERATION
         * @see #getTypeBasedWhitelist(Class...)
         */
        public static final Predicate<Exception> IGNORE_UNSUPPORTED_AND_UNSOLVED = getTypeBasedWhitelist(
                UnsupportedOperationException.class, UnsolvedSymbolException.class);

        /**
         * @see CombinedTypeSolver#setFilter(Predicate)
         * @see #getTypeBasedWhitelist(Class...)
         * 
         * @return A filter that ignores an exception if <b>none</b> of the listed classes are
         *         {@link Class#isAssignableFrom(Class) assignable from}
         *         the thrown exception class.
         */
        public static Predicate<Exception> getTypeBasedBlacklist(Class<? extends Exception>... blacklist) {
            return e -> {
                for (Class<? extends Exception> clazz : blacklist) {
                    if (clazz.isAssignableFrom(e.getClass())) {
                        return false;
                    }
                }
                return true;
            };
        }

        /**
         * @see CombinedTypeSolver#setFilter(Predicate)
         * @see #getTypeBasedBlacklist(Class...)
         * 
         * @return A filter that ignores an exception if <b>any</b> of the listed classes are
         *         {@link Class#isAssignableFrom(Class) assignable from}
         *         the thrown exception class.
         */
        public static Predicate<Exception> getTypeBasedWhitelist(Class<? extends Exception>... whitelist) {
            return e -> {
                for (Class<? extends Exception> clazz : whitelist) {
                    if (clazz.isAssignableFrom(e.getClass())) {
                        return true;
                    }
                }
                return false;
            };
        }
    }
}
