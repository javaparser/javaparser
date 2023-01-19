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

package com.github.javaparser.resolution.logic;

import com.github.javaparser.resolution.MethodAmbiguityException;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedConstructorDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.types.ResolvedArrayType;
import com.github.javaparser.resolution.types.ResolvedType;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

/**
 * @author Fred Lefévère-Laoide
 */
public class ConstructorResolutionLogic {

    private static List<ResolvedType> groupVariadicParamValues(List<ResolvedType> argumentsTypes, int startVariadic,
                                                               ResolvedType variadicType) {
        List<ResolvedType> res = new ArrayList<>(argumentsTypes.subList(0, startVariadic));
        List<ResolvedType> variadicValues = argumentsTypes.subList(startVariadic, argumentsTypes.size());
        if (variadicValues.isEmpty()) {
            // TODO if there are no variadic values we should default to the bound of the formal type
            res.add(variadicType);
        } else {
            ResolvedType componentType = findCommonType(variadicValues);
            res.add(new ResolvedArrayType(componentType));
        }
        return res;
    }

    private static ResolvedType findCommonType(List<ResolvedType> variadicValues) {
        if (variadicValues.isEmpty()) {
            throw new IllegalArgumentException();
        }
        // TODO implement this decently
        return variadicValues.get(0);
    }

    public static boolean isApplicable(ResolvedConstructorDeclaration constructor, List<ResolvedType> argumentsTypes,
                                       TypeSolver typeSolver) {
        return isApplicable(constructor, argumentsTypes, typeSolver, false);
    }

    private static boolean isApplicable(ResolvedConstructorDeclaration constructor, List<ResolvedType> argumentsTypes,
                                        TypeSolver typeSolver, boolean withWildcardTolerance) {
        if (constructor.hasVariadicParameter()) {
            int pos = constructor.getNumberOfParams() - 1;
            if (constructor.getNumberOfParams() == argumentsTypes.size()) {
                // check if the last value is directly assignable as an array
                ResolvedType expectedType = constructor.getLastParam().getType();
                ResolvedType actualType = argumentsTypes.get(pos);
                if (!expectedType.isAssignableBy(actualType)) {
                    for (ResolvedTypeParameterDeclaration tp : constructor.getTypeParameters()) {
                        expectedType = MethodResolutionLogic.replaceTypeParam(expectedType, tp, typeSolver);
                    }
                    if (!expectedType.isAssignableBy(actualType)) {
                        if (actualType.isArray()
                                && expectedType.isAssignableBy(actualType.asArrayType().getComponentType())) {
                            argumentsTypes.set(pos, actualType.asArrayType().getComponentType());
                        } else {
                            argumentsTypes = groupVariadicParamValues(argumentsTypes, pos,
                                    constructor.getLastParam().getType());
                        }
                    }
                } // else it is already assignable, nothing to do
            } else {
                if (pos > argumentsTypes.size()) {
                    return false;
                }
                argumentsTypes =
                        groupVariadicParamValues(argumentsTypes, pos, constructor.getLastParam().getType());
            }
        }

        if (constructor.getNumberOfParams() != argumentsTypes.size()) {
            return false;
        }
        Map<String, ResolvedType> matchedParameters = new HashMap<>();
        boolean needForWildCardTolerance = false;
        for (int i = 0; i < constructor.getNumberOfParams(); i++) {
            ResolvedType expectedType = constructor.getParam(i).getType();
            ResolvedType actualType = argumentsTypes.get(i);
            if ((expectedType.isTypeVariable() && !(expectedType.isWildcard()))
                    && expectedType.asTypeParameter().declaredOnMethod()) {
                matchedParameters.put(expectedType.asTypeParameter().getName(), actualType);
                continue;
            }
            boolean isAssignableWithoutSubstitution =
                    expectedType.isAssignableBy(actualType) || (constructor.getParam(i).isVariadic()
                            && new ResolvedArrayType(expectedType).isAssignableBy(actualType));
            if (!isAssignableWithoutSubstitution && expectedType.isReferenceType()
                    && actualType.isReferenceType()) {
                isAssignableWithoutSubstitution = MethodResolutionLogic.isAssignableMatchTypeParameters(
                        expectedType.asReferenceType(), actualType.asReferenceType(), matchedParameters);
            }
            if (!isAssignableWithoutSubstitution) {
                for (ResolvedTypeParameterDeclaration tp : constructor.getTypeParameters()) {
                    expectedType = MethodResolutionLogic.replaceTypeParam(expectedType, tp, typeSolver);
                }
                for (ResolvedTypeParameterDeclaration tp : constructor.declaringType().getTypeParameters()) {
                    expectedType = MethodResolutionLogic.replaceTypeParam(expectedType, tp, typeSolver);
                }

                if (!expectedType.isAssignableBy(actualType)) {
                    if (actualType.isWildcard() && withWildcardTolerance && !expectedType.isPrimitive()) {
                        needForWildCardTolerance = true;
                        continue;
                    }
                    if (constructor.hasVariadicParameter() && i == constructor.getNumberOfParams() - 1) {
                        if (new ResolvedArrayType(expectedType).isAssignableBy(actualType)) {
                            continue;
                        }
                    }
                    return false;
                }
            }
        }
        return !withWildcardTolerance || needForWildCardTolerance;
    }

    /**
     * @param constructors        we expect the methods to be ordered such that inherited methods are later in the list
     * @param argumentsTypes
     * @param typeSolver
     * @return
     */
    public static SymbolReference<ResolvedConstructorDeclaration> findMostApplicable(
            List<ResolvedConstructorDeclaration> constructors, List<ResolvedType> argumentsTypes, TypeSolver typeSolver) {
        SymbolReference<ResolvedConstructorDeclaration> res =
                findMostApplicable(constructors, argumentsTypes, typeSolver, false);
        if (res.isSolved()) {
            return res;
        }
        return findMostApplicable(constructors, argumentsTypes, typeSolver, true);
    }

    public static SymbolReference<ResolvedConstructorDeclaration> findMostApplicable(
            List<ResolvedConstructorDeclaration> constructors, List<ResolvedType> argumentsTypes, TypeSolver typeSolver, boolean wildcardTolerance) {
        List<ResolvedConstructorDeclaration> applicableConstructors = constructors.stream().filter((m) -> isApplicable(m, argumentsTypes, typeSolver, wildcardTolerance)).collect(Collectors.toList());
        if (applicableConstructors.isEmpty()) {
            return SymbolReference.unsolved();
        }
        if (applicableConstructors.size() == 1) {
            return SymbolReference.solved(applicableConstructors.get(0));
        } else {
            ResolvedConstructorDeclaration winningCandidate = applicableConstructors.get(0);
            ResolvedConstructorDeclaration other = null;
            boolean possibleAmbiguity = false;
            for (int i = 1; i < applicableConstructors.size(); i++) {
                other = applicableConstructors.get(i);
                if (isMoreSpecific(winningCandidate, other, typeSolver)) {
                    possibleAmbiguity = false;
                } else if (isMoreSpecific(other, winningCandidate, typeSolver)) {
                    possibleAmbiguity = false;
                    winningCandidate = other;
                } else {
                    if (winningCandidate.declaringType().getQualifiedName()
                            .equals(other.declaringType().getQualifiedName())) {
                        possibleAmbiguity = true;
                    } else {
                        // we expect the methods to be ordered such that inherited methods are later in the list
                    }
                }
                if (possibleAmbiguity) {
                    // pick the first exact match if it exists
                    if (!MethodResolutionLogic.isExactMatch(winningCandidate, argumentsTypes)) {
                        if (MethodResolutionLogic.isExactMatch(other, argumentsTypes)) {
                            winningCandidate = other;
                        } else {
                            throw new MethodAmbiguityException("Ambiguous constructor call: cannot find a most applicable constructor: " + winningCandidate + ", " + other);
                        }
                    }
                }
            }
            
            return SymbolReference.solved(winningCandidate);
        }
    }

    private static boolean isMoreSpecific(ResolvedConstructorDeclaration constructorA,
                                          ResolvedConstructorDeclaration constructorB, TypeSolver typeSolver) {
        boolean oneMoreSpecificFound = false;
        if (constructorA.getNumberOfParams() < constructorB.getNumberOfParams()) {
            return true;
        }
        if (constructorA.getNumberOfParams() > constructorB.getNumberOfParams()) {
            return false;
        }
        for (int i = 0; i < constructorA.getNumberOfParams(); i++) {
            ResolvedType tdA = constructorA.getParam(i).getType();
            ResolvedType tdB = constructorB.getParam(i).getType();
            // B is more specific
            if (tdB.isAssignableBy(tdA) && !tdA.isAssignableBy(tdB)) {
                oneMoreSpecificFound = true;
            }
            // A is more specific
            if (tdA.isAssignableBy(tdB) && !tdB.isAssignableBy(tdA)) {
                return false;
            }
            // if it matches a variadic and a not variadic I pick the not variadic
            if (!tdA.isArray() && tdB.isArray()) {
                return true;
            }
            // FIXME
            if (i == (constructorA.getNumberOfParams() - 1) && tdA.arrayLevel() > tdB.arrayLevel()) {
                return true;
            }
        }
        return oneMoreSpecificFound;
    }

}
