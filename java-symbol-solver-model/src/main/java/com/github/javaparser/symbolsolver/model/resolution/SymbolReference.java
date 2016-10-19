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

package com.github.javaparser.symbolsolver.model.resolution;

import com.github.javaparser.symbolsolver.model.declarations.Declaration;

import java.util.Optional;

/**
 * @author Federico Tomassetti
 */
public class SymbolReference<S extends Declaration> {

    private Optional<? extends S> correspondingDeclaration;

    private SymbolReference(Optional<? extends S> correspondingDeclaration) {
        this.correspondingDeclaration = correspondingDeclaration;
    }

    public static <S extends Declaration, S2 extends S> SymbolReference<S> solved(S2 symbolDeclaration) {
        return new SymbolReference(Optional.of(symbolDeclaration));
    }

    public static <S extends Declaration, S2 extends S> SymbolReference<S> unsolved(Class<S2> clazz) {
        return new SymbolReference(Optional.<S>empty());
    }

    @Override
    public String toString() {
        return "SymbolReference{" + correspondingDeclaration + "}";
    }

    public S getCorrespondingDeclaration() {
        if (!isSolved()) {
            throw new IllegalStateException();
        }
        return correspondingDeclaration.get();
    }

    public boolean isSolved() {
        return correspondingDeclaration.isPresent();
    }
}
