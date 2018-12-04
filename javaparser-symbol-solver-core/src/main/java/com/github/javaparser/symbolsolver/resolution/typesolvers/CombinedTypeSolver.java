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
    
    /**
     * A predicate which determines what to do if an exception is raised during the parsing process.
     * If it returns <code>true</code> the exception will be ignored, and solving will continue using the next solver in line.
     * If it returns <code>false</code> the exception will be thrown, stopping the solving process.
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
        this(ExceptionHandlers.IGNORE_NONE, elements);
    }

    /** @see #exceptionHandler */
    public CombinedTypeSolver(Predicate<Exception> exceptionHandler, TypeSolver... elements) {
        setExceptionHandler(exceptionHandler);

        for (TypeSolver el : elements) {
            add(el);
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
                if (!exceptionHandler.test(e)) { // we shouldn't ignore this exception
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
