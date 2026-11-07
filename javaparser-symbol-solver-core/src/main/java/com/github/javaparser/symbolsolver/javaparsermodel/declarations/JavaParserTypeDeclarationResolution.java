/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2026 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.javaparsermodel.declarations;

import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.resolution.Context;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.function.Supplier;

/**
 * Common resolution logic for JavaParser class and record declarations.
 *
 * <p>This class contains only the parts that are identical between the two declarations. The
 * class- and record-specific behavior (superclass lookup, implicit record members, etc.) remains in
 * the declarations themselves.
 */
final class JavaParserTypeDeclarationResolution {

    private JavaParserTypeDeclarationResolution() {}

    static <T extends TypeDeclaration<?>> List<ResolvedReferenceType> getAncestors(
            ResolvedReferenceTypeDeclaration declaration,
            T wrappedNode,
            List<ClassOrInterfaceType> implementedTypes,
            Supplier<Optional<ResolvedReferenceType>> superClassSupplier,
            Function<ClassOrInterfaceType, ResolvedReferenceType> toReferenceType,
            boolean acceptIncompleteList) {
        List<ResolvedReferenceType> ancestors = new ArrayList<>();

        // We want to avoid infinite recursion in case of Object having Object as ancestor
        if (declaration.isJavaLangObject()) {
            return ancestors;
        }

        Optional<String> qualifiedName = wrappedNode.getFullyQualifiedName();
        if (!qualifiedName.isPresent()) {
            return ancestors;
        }

        try {
            // If a superclass is found, add it as an ancestor
            Optional<ResolvedReferenceType> superClass = superClassSupplier.get();
            if (superClass.isPresent()) {
                if (isAncestor(superClass.get(), qualifiedName.get())) {
                    ancestors.add(superClass.get());
                }
            }
        } catch (UnsolvedSymbolException e) {
            // in case we could not resolve the super class, we may still be able to resolve (some of) the
            // implemented interfaces and so we continue gracefully with an (incomplete) list of ancestors

            if (!acceptIncompleteList) {
                // Only throw if an incomplete ancestor list is unacceptable.
                throw e;
            }
        }

        for (ClassOrInterfaceType implemented : implementedTypes) {
            try {
                // If an implemented interface is found, add it as an ancestor
                ResolvedReferenceType rrt = toReferenceType.apply(implemented);
                if (isAncestor(rrt, qualifiedName.get())) {
                    ancestors.add(rrt);
                }
            } catch (UnsolvedSymbolException e) {
                // in case we could not resolve some implemented interface, we may still be able to resolve the
                // extended class or (some of) the other implemented interfaces and so we continue gracefully
                // with an (incomplete) list of ancestors

                if (!acceptIncompleteList) {
                    // Only throw if an incomplete ancestor list is unacceptable.
                    throw e;
                }
            }
        }

        return ancestors;
    }

    static <T extends TypeDeclaration<?>> SymbolReference<ResolvedTypeDeclaration> solveType(
            ResolvedTypeDeclaration self,
            T wrappedNode,
            Function<String, SymbolReference<ResolvedTypeDeclaration>> adapterSolver,
            Supplier<Context> contextSupplier,
            String name,
            BiFunction<T, String, SymbolReference<ResolvedTypeDeclaration>> nestedSolver) {
        if (wrappedNode.getName().getId().equals(name)) {
            return SymbolReference.solved(self);
        }
        SymbolReference<ResolvedTypeDeclaration> ref = adapterSolver.apply(name);
        if (ref.isSolved()) {
            return ref;
        }

        String prefix = wrappedNode.getName().asString() + ".";
        if (name.startsWith(prefix) && name.length() > prefix.length()) {
            return nestedSolver.apply(wrappedNode, name.substring(prefix.length()));
        }

        return contextSupplier
                .get()
                .getParent()
                .orElseThrow(() -> new RuntimeException("Parent context unexpectedly empty."))
                .solveType(name);
    }

    private static boolean isAncestor(ResolvedReferenceType candidateAncestor, String ownQualifiedName) {
        Optional<ResolvedReferenceTypeDeclaration> resolvedReferenceTypeDeclaration =
                candidateAncestor.getTypeDeclaration();
        if (resolvedReferenceTypeDeclaration.isPresent()) {
            ResolvedTypeDeclaration rtd = resolvedReferenceTypeDeclaration.get().asType();
            // do not consider an inner or nested type as an ancestor
            return !rtd.hasInternalType(ownQualifiedName);
        }
        return false;
    }
}
