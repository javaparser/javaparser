/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2020 The JavaParser Team.
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

import com.github.javaparser.quality.Nullable;
import com.github.javaparser.resolution.declarations.ResolvedDeclaration;

import java.util.Optional;

/**
 * A reference to a symbol. It can solved or not solved. If solved the corresponding
 * declaration will be provided.
 *
 * @author Federico Tomassetti
 */
public class SymbolReference<S extends ResolvedDeclaration> {

    private final S correspondingDeclaration;

    private SymbolReference(@Nullable S correspondingDeclaration) {
        this.correspondingDeclaration = correspondingDeclaration;
    }

    /**
     * Create a solve reference to the given symbol.
     */
    public static <S extends ResolvedDeclaration, S2 extends S> SymbolReference<S> solved(S2 symbolDeclaration) {
        return new SymbolReference<>(symbolDeclaration);
    }

    /**
     * Create a reference for an unsolved symbol.
     *
     * @return The created unsolved symbol reference.
     *
     * @param <S> The symbol reference type.
     */
    public static <S extends ResolvedDeclaration> SymbolReference<S> unsolved() {
        return new SymbolReference<>(null);
    }

    /**
     * Create an unsolved reference specifying the type of the value expected.
     */
    public static <S extends ResolvedDeclaration, S2 extends S> SymbolReference<S> unsolved(Class<S2> clazz) {
        return new SymbolReference<>(null);
    }

    @Override
    public String toString() {
        return "SymbolReference{" + correspondingDeclaration + "}";
    }

    /**
     * Get the declaration associated with the Symbol.
     *
     * @return an {@link Optional} with a present value if the symbol is solved, otherwise an empty {@link Optional}.
     */
    public Optional<S> getDeclaration() {
        return Optional.ofNullable(correspondingDeclaration);
    }

    /**
     * The corresponding declaration. If not solve this throws UnsupportedOperationException.
     *
     * @deprecated This function is deprecated. Please consider using {@link #getDeclaration()}
     */
    @Deprecated
    public S getCorrespondingDeclaration() {

        Optional<S> declaration = getDeclaration();
        if (declaration.isPresent()) {
            return declaration.get();
        }

        throw new UnsupportedOperationException("CorrespondingDeclaration not available for unsolved symbol.");
    }

    /**
     * Is the reference solved?
     *
     * @deprecated To check if the reference is solved, please consider using {@link #getDeclaration()}
     *             followed by {@link Optional#isPresent()}.
     */
    @Deprecated
    public boolean isSolved() {
        return getDeclaration().isPresent();
    }

    public static <O extends ResolvedDeclaration> SymbolReference<O> adapt(SymbolReference<? extends O> ref, Class<O> clazz) {
        return ref.getDeclaration()
                .<SymbolReference<O>>map(SymbolReference::solved)
                .orElseGet(() -> SymbolReference.unsolved(clazz));
    }
}
