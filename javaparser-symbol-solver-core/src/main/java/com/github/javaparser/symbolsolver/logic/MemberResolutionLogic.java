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

package com.github.javaparser.symbolsolver.logic;

import com.github.javaparser.resolution.Context;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.logic.MethodResolutionLogic;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.core.resolution.TypeVariableResolutionCapability;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

/**
 * Looks up members of a type: the methods it declares plus the ones it inherits from its ancestors.
 * <p>
 * This is deliberately narrower than a lexical lookup. A member lookup answers "does this type have
 * such a member?", so it stops at the type and its hierarchy; it never consults the compilation unit
 * the type happens to be declared in, because imports are a property of that file and not members of
 * the type (JLS 7.5.3, 7.5.4).
 *
 * @author Federico Tomassetti
 */
public class MemberResolutionLogic {

    private MemberResolutionLogic() {
        // This class is meant to be used statically only.
    }

    /**
     * Collects the methods named {@code name} that {@code typeDeclaration} declares or inherits.
     *
     * @return a mutable list, so that callers can keep adding candidates of their own.
     */
    public static List<ResolvedMethodDeclaration> collectCandidateMembers(
            ResolvedReferenceTypeDeclaration typeDeclaration,
            String name,
            List<ResolvedType> argumentsTypes,
            boolean staticOnly) {

        // Begin by locating methods declared "here"
        List<ResolvedMethodDeclaration> candidateMethods = typeDeclaration.getDeclaredMethods().stream()
                .filter(m -> m.getName().equals(name))
                .filter(m -> !staticOnly || m.isStatic())
                .collect(Collectors.toCollection(ArrayList::new));

        // Next, consider methods declared within ancestors.
        // Note that we only consider ancestors when we are not currently at java.lang.Object (avoiding infinite
        // recursion).
        if (!typeDeclaration.isJavaLangObject()) {
            for (ResolvedReferenceType ancestor : typeDeclaration.getAncestors(true)) {
                Optional<ResolvedReferenceTypeDeclaration> ancestorTypeDeclaration = ancestor.getTypeDeclaration();

                // Avoid recursion on self
                if (ancestorTypeDeclaration.isPresent() && typeDeclaration != ancestorTypeDeclaration.get()) {
                    // Consider methods declared on self
                    candidateMethods.addAll(ancestor.getAllMethodsVisibleToInheritors().stream()
                            .filter(m -> m.getName().equals(name))
                            .collect(Collectors.toList()));

                    // consider methods from superclasses and only default methods from interfaces :
                    // not true, we should keep abstract as a valid candidate
                    // abstract are removed in MethodResolutionLogic.isApplicable is necessary
                    SymbolReference<ResolvedMethodDeclaration> res = MethodResolutionLogic.solveMethodInType(
                            ancestorTypeDeclaration.get(), name, argumentsTypes, staticOnly);
                    if (res.isSolved()) {
                        candidateMethods.add(res.getCorrespondingDeclaration());
                    }
                }
            }
        }

        return candidateMethods;
    }

    /**
     * Solves a method among the members of {@code typeDeclaration}: the ones it declares and the ones it
     * inherits, and nothing else.
     */
    public static SymbolReference<ResolvedMethodDeclaration> solveMethodInMembers(
            ResolvedReferenceTypeDeclaration typeDeclaration,
            String name,
            List<ResolvedType> argumentsTypes,
            boolean staticOnly,
            TypeSolver typeSolver) {

        List<ResolvedMethodDeclaration> candidateMethods =
                collectCandidateMembers(typeDeclaration, name, argumentsTypes, staticOnly);

        // if is interface and candidate method list is empty, we should check the Object Methods
        if (candidateMethods.isEmpty() && typeDeclaration.isInterface()) {
            SymbolReference<ResolvedMethodDeclaration> res = MethodResolutionLogic.solveMethodInType(
                    typeSolver.getSolvedJavaLangObject(), name, argumentsTypes, false);
            if (res.isSolved()) {
                candidateMethods.add(res.getCorrespondingDeclaration());
            }
        }

        return MethodResolutionLogic.findMostApplicable(candidateMethods, name, argumentsTypes, typeSolver);
    }

    /**
     * Solves a method among the members of {@code typeDeclaration} and resolves its type variables, so that
     * the result can be used as a {@link MethodUsage}.
     *
     * @param context the context the resulting usage is resolved against; it is not searched for candidates.
     */
    public static Optional<MethodUsage> solveMethodAsUsageInMembers(
            ResolvedReferenceTypeDeclaration typeDeclaration,
            String name,
            List<ResolvedType> argumentsTypes,
            Context context,
            TypeSolver typeSolver) {

        SymbolReference<ResolvedMethodDeclaration> methodSolved =
                solveMethodInMembers(typeDeclaration, name, argumentsTypes, false, typeSolver);
        if (!methodSolved.isSolved()) {
            return Optional.empty();
        }

        ResolvedMethodDeclaration methodDeclaration = methodSolved.getCorrespondingDeclaration();
        if (!(methodDeclaration instanceof TypeVariableResolutionCapability)) {
            throw new UnsupportedOperationException(String.format(
                    "Resolved method declarations must implement %s.",
                    TypeVariableResolutionCapability.class.getName()));
        }
        return Optional.of(
                ((TypeVariableResolutionCapability) methodDeclaration).resolveTypeVariables(context, argumentsTypes));
    }
}
