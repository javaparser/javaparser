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

package me.tomassetti.symbolsolver.model.resolution;

import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;

/**
 * @author Federico Tomassetti
 */
public interface TypeSolver {

    default TypeSolver getRoot() {
        if (getParent() == null) {
            return this;
        } else {
            return getParent().getRoot();
        }
    }

    TypeSolver getParent();

    void setParent(TypeSolver parent);

    SymbolReference<TypeDeclaration> tryToSolveType(String name);

    default TypeDeclaration solveType(String name) throws UnsolvedSymbolException {
        SymbolReference<TypeDeclaration> ref = tryToSolveType(name);
        if (ref.isSolved()) {
            return ref.getCorrespondingDeclaration();
        } else {
            throw new UnsolvedSymbolException(name, this);
        }
    }

}
