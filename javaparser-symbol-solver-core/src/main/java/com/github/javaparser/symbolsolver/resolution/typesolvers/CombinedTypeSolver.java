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
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.symbolsolver.cache.Cache;
import com.github.javaparser.symbolsolver.cache.InMemoryCache;

import java.util.*;
import java.util.function.Predicate;

/**
 * A container for type solvers. All solving is done by the contained type solvers.
 * This helps you when an API asks for a single type solver, but you need several.
 *
 * @author Federico Tomassetti
 */
public class CombinedTypeSolver implements TypeSolver {

    private final Cache<String, SymbolReference<ResolvedReferenceTypeDeclaration>> typeCache;

    private TypeSolver parent;
    private List<TypeSolver> elements = new ArrayList<>();
    
    /**
     * A predicate which determines what to do if an exception is raised during the parsing process.
     * If it returns {@code true} the exception will be ignored, and solving will continue using the next solver in line.
     * If it returns {@code false} the exception will be thrown, stopping the solving process.
     * 
     * Main use case for this is to circumvent bugs or missing functionality in some type solvers.
     * If for example solver A has a bug resulting in a {@link NullPointerException}, you could use a {@link ExceptionHandlers#getTypeBasedWhitelist(Class...) whitelist} to ignore that type of exception.
     * A secondary solver would then be able to step in when such an error occurs.
     * 
     * @see #CombinedTypeSolver(Predicate, TypeSolver...)
     * @see #setExceptionHandler(Predicate)
     */
    private Predicate<Exception> exceptionHandler;

    public CombinedTypeSolver(TypeSolver... elements) {
        this(Arrays.asList(elements));
    }

    public CombinedTypeSolver(Predicate<Exception> exceptionHandler, TypeSolver... elements) {
        this(exceptionHandler, Arrays.asList(elements));
    }

    public CombinedTypeSolver(Iterable<TypeSolver> elements) {
        this(ExceptionHandlers.IGNORE_NONE, elements);
    }

    /** @see #exceptionHandler */
    public CombinedTypeSolver(Predicate<Exception> exceptionHandler, Iterable<TypeSolver> elements) {
        this(exceptionHandler, elements, InMemoryCache.create());
    }

    /**
     * Create a new instance of {@link CombinedTypeSolver} with a custom symbol cache.
     *
     * @param exceptionHandler  How exception should be handled.
     * @param elements          The list of elements to include by default.
     * @param typeCache       The cache to be used to store symbols.
     *
     * @see #exceptionHandler
     */
    public CombinedTypeSolver(Predicate<Exception> exceptionHandler,
                              Iterable<TypeSolver> elements,
                              Cache<String, SymbolReference<ResolvedReferenceTypeDeclaration>> typeCache) {
        Objects.requireNonNull(typeCache, "The typeCache can't be null.");

        setExceptionHandler(exceptionHandler);
        this.typeCache = typeCache;

        for (TypeSolver el : elements) {
            add(el, false);
        }
    }

    /** @see #exceptionHandler */
    public void setExceptionHandler(Predicate<Exception> exceptionHandler) {
        this.exceptionHandler = exceptionHandler;
    }

    @Override
    public TypeSolver getParent() {
        return parent;
    }

    @Override
    public void setParent(TypeSolver parent) {
        Objects.requireNonNull(parent);
        if (this.parent != null) {
            throw new IllegalStateException("This TypeSolver already has a parent.");
        }
        if (parent == this) {
            throw new IllegalStateException("The parent of this TypeSolver cannot be itself.");
        }
        this.parent = parent;
    }

    /**
     * Append a type solver to the current solver.
     *
     * @param typeSolver The type solver to be appended.
     * @param resetCache If should reset the cache when the solver is inserted.
     */
    public void add(TypeSolver typeSolver, boolean resetCache) {
        Objects.requireNonNull(typeSolver, "The type solver can't be null");

        this.elements.add(typeSolver);
        typeSolver.setParent(this);

        // Check if the cache should be reset after inserting
        if (resetCache) {
            typeCache.removeAll();
        }
    }

    /**
     * Append a type solver to the current solver.
     * <br>
     * By default the cached values will be removed.
     *
     * @param typeSolver The type solver to be appended.
     */
    public void add(TypeSolver typeSolver) {
        add(typeSolver, true);
    }

    @Override
    public SymbolReference<ResolvedReferenceTypeDeclaration> tryToSolveType(String name) {
        Optional<SymbolReference<ResolvedReferenceTypeDeclaration>> cachedSymbol = typeCache.get(name);
        if (cachedSymbol.isPresent()) {
            return cachedSymbol.get();
        }

        // If the symbol is not cached
        for (TypeSolver ts : elements) {
            try {
                SymbolReference<ResolvedReferenceTypeDeclaration> res = ts.tryToSolveType(name);
                if (res.isSolved()) {
                    typeCache.put(name, res);
                    return res;
                }
            } catch (Exception e) {
                if (!exceptionHandler.test(e)) { // we shouldn't ignore this exception
                    throw e;
                }
            }
        }

        // When unable to solve, cache the value with unsolved symbol
        SymbolReference<ResolvedReferenceTypeDeclaration> unsolvedSymbol = SymbolReference.unsolved();
        typeCache.put(name, unsolvedSymbol);
        return unsolvedSymbol;
    }

    @Override
    public ResolvedReferenceTypeDeclaration solveType(String name) throws UnsolvedSymbolException {
        SymbolReference<ResolvedReferenceTypeDeclaration> res = tryToSolveType(name);
        if (res.isSolved()) {
            return res.getCorrespondingDeclaration();
        }
        throw new UnsolvedSymbolException(name);
    }

    /**
     * Provides some convenience exception handler implementations
     * @see CombinedTypeSolver#setExceptionHandler(Predicate)
     */
    public static class ExceptionHandlers {

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
         * @see CombinedTypeSolver#setExceptionHandler(Predicate)
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
         * @see CombinedTypeSolver#setExceptionHandler(Predicate)
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
