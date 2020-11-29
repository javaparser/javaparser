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

import com.github.javaparser.resolution.declarations.ResolvedDeclaration;

import java.util.Optional;

/**
 * A reference to a symbol. It can solved or not solved. If solved the corresponding
 * declaration will be provided.
 *
 * @author Federico Tomassetti
 */
public class SymbolReference<S extends ResolvedDeclaration> {

    private Optional<? extends S> correspondingDeclaration;

    private SymbolReference(Optional<? extends S> correspondingDeclaration) {
        this.correspondingDeclaration = correspondingDeclaration;
    }

    /**
     * Create a solve reference to the given symbol.
     */
    public static <S extends ResolvedDeclaration, S2 extends S> SymbolReference<S> solved(S2 symbolDeclaration) {
        return new SymbolReference<S>(Optional.of(symbolDeclaration));
    }

    /**
     * Create an unsolved reference specifying the type of the value expected.
     */
    public static <S extends ResolvedDeclaration, S2 extends S> SymbolReference<S> unsolved(Class<S2> clazz) {
        return new SymbolReference<>(Optional.empty());
    }

    @Override
    public String toString() {
        return "SymbolReference{" + correspondingDeclaration + "}";
    }

    /**
     * The corresponding declaration. If not solve this throws UnsupportedOperationException.
     * // TODO: Convert this to returning Optional.
     */
    public S getCorrespondingDeclaration() {
        if (!isSolved()) {
            throw new UnsupportedOperationException("CorrespondingDeclaration not available for unsolved symbol.");
        }
        return correspondingDeclaration.get();
    }

    /**
     * Is the reference solved?
     */
    public boolean isSolved() {
        return correspondingDeclaration.isPresent();
    }

    public static <O extends ResolvedDeclaration> SymbolReference<O> adapt(SymbolReference<? extends O> ref, Class<O> clazz) {
        if (ref.isSolved()) {
            return SymbolReference.solved(ref.getCorrespondingDeclaration());
        } else {
            return SymbolReference.unsolved(clazz);
        }
    }
}
