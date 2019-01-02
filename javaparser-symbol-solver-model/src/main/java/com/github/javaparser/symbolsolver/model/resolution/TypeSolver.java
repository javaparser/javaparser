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

import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;

/**
 * An element able to find TypeDeclaration from their name.
 * TypeSolvers are organized in hierarchies.
 *
 * @author Federico Tomassetti
 */
public interface TypeSolver {

    /**
     * Get the root of the hierarchy of type solver.
     */
    default TypeSolver getRoot() {
        if (getParent() == null) {
            return this;
        } else {
            return getParent().getRoot();
        }
    }

    /**
     * Parent of the this TypeSolver. This can return null.
     */
    TypeSolver getParent();

    /**
     * Set the parent of this TypeSolver.
     */
    void setParent(TypeSolver parent);

    /**
     * Try to solve the type with the given name. It always return a SymbolReference which can be solved
     * or unsolved.
     */
    SymbolReference<ResolvedReferenceTypeDeclaration> tryToSolveType(String name);

    /**
     * Solve the given type. Either the type is found and returned or an UnsolvedSymbolException is thrown.
     */
    default ResolvedReferenceTypeDeclaration solveType(String name) throws UnsolvedSymbolException {
        SymbolReference<ResolvedReferenceTypeDeclaration> ref = tryToSolveType(name);
        if (ref.isSolved()) {
            return ref.getCorrespondingDeclaration();
        } else {
            throw new UnsolvedSymbolException(name, this.toString());
        }
    }

    default boolean hasType(String name) {
        return tryToSolveType(name).isSolved();
    }
}
