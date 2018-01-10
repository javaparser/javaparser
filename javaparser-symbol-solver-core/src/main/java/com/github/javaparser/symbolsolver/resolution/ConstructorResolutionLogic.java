/*
 * Copyright 2016 Federico Tomassetti
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 * in compliance with the License. You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software distributed under the License
 * is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
 * or implied. See the License for the specific language governing permissions and limitations under
 * the License.
 */

package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.resolution.MethodAmbiguityException;
import com.github.javaparser.resolution.declarations.ResolvedConstructorDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.types.ResolvedArrayType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;

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
                List<ResolvedTypeParameterDeclaration> typeParameters = constructor.getTypeParameters();
                typeParameters.addAll(constructor.declaringType().getTypeParameters());
                for (ResolvedTypeParameterDeclaration tp : typeParameters) {
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
            return SymbolReference.unsolved(ResolvedConstructorDeclaration.class);
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
            // FIXME
            if (i == (constructorA.getNumberOfParams() - 1) && tdA.arrayLevel() > tdB.arrayLevel()) {
                return true;
            }
        }
        return oneMoreSpecificFound;
    }

}
