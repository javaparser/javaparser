/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2024 The JavaParser Team.
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
package com.github.javaparser.resolution;

import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.model.SymbolReference;

/**
 * An element able to find TypeDeclaration from their name.
 * TypeSolvers are organized in hierarchies.
 *
 * @author Federico Tomassetti
 */
public interface TypeSolver {

    String JAVA_LANG_OBJECT = Object.class.getCanonicalName();

    // Can't use java.lang.Record.class.getCanonicalName() since records were only added in Java 14.
    String JAVA_LANG_RECORD = "java.lang.Record";

    /**
     * Get the root of the hierarchy of type solver.
     */
    default TypeSolver getRoot() {
        if (getParent() == null) {
            return this;
        }
        return getParent().getRoot();
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
        }
        throw new UnsolvedSymbolException(name, this.toString());
    }

    SymbolReference<ResolvedReferenceTypeDeclaration> tryToSolveTypeInModule(String qualifiedModuleName, String simpleTypeName);

    default ResolvedReferenceTypeDeclaration solveTypeInModule(String qualifiedModuleName, String simpleTypeName) {
        SymbolReference<ResolvedReferenceTypeDeclaration> ref = tryToSolveTypeInModule(qualifiedModuleName, simpleTypeName);
        if (ref.isSolved()) {
            return ref.getCorrespondingDeclaration();
        }
        throw new UnsolvedSymbolException(simpleTypeName, "module=" + qualifiedModuleName + " in " + this);
    }

    /**
     * @return A resolved reference to {@code java.lang.Object}
     */
    default ResolvedReferenceTypeDeclaration getSolvedJavaLangObject() throws UnsolvedSymbolException {
        return solveType(JAVA_LANG_OBJECT);
    }

    /**
     * @return A resolved reference to {@code java.lang.Record}
     */
    default ResolvedReferenceTypeDeclaration getSolvedJavaLangRecord() throws UnsolvedSymbolException {
        return solveType(JAVA_LANG_RECORD);
    }

    default boolean hasType(String name) {
        return tryToSolveType(name).isSolved();
    }
}
