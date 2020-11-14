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

package com.github.javaparser.symbolsolver.resolution;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import com.github.javaparser.resolution.MethodAmbiguityException;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedMethodLikeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedParameterDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.types.ResolvedArrayType;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.resolution.types.ResolvedTypeVariable;
import com.github.javaparser.resolution.types.ResolvedWildcard;
import com.github.javaparser.symbolsolver.logic.MethodResolutionCapability;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;

/**
 * @author Federico Tomassetti
 */
public class MethodResolutionLogic {

    private static List<ResolvedType> groupVariadicParamValues(List<ResolvedType> argumentsTypes, int startVariadic, ResolvedType variadicType) {
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

    public static boolean isApplicable(ResolvedMethodDeclaration method, String name, List<ResolvedType> argumentsTypes, TypeSolver typeSolver) {
        return isApplicable(method, name, argumentsTypes, typeSolver, false);
    }

    /**
     * Note the specific naming here -- parameters are part of the method declaration,
     * while arguments are the values passed when calling a method.
     * Note that "needle" refers to that value being used as a search/query term to match against.
     *
     * @return true, if the given ResolvedMethodDeclaration matches the given name/types (normally obtained from a MethodUsage)
     *
     * @see {@link MethodResolutionLogic#isApplicable(MethodUsage, String, List, TypeSolver)}
     */
    private static boolean isApplicable(ResolvedMethodDeclaration methodDeclaration, String needleName, List<ResolvedType> needleArgumentTypes, TypeSolver typeSolver, boolean withWildcardTolerance) {
        if (!methodDeclaration.getName().equals(needleName)) {
            return false;
        }

        // The index of the final method parameter (on the method declaration).
        int countOfMethodParametersDeclared = methodDeclaration.getNumberOfParams();
        int lastMethodParameterIndex = Math.max(0, countOfMethodParametersDeclared - 1);

        // The index of the final argument passed (on the method usage).
        int countOfNeedleArgumentsPassed = needleArgumentTypes.size();
        int lastNeedleArgumentIndex = Math.max(0, countOfNeedleArgumentsPassed - 1);

        boolean methodIsDeclaredWithVariadicParameter = methodDeclaration.hasVariadicParameter();

        if (!methodIsDeclaredWithVariadicParameter && (countOfNeedleArgumentsPassed != countOfMethodParametersDeclared)) {
            // If it is not variadic, and the number of parameters/arguments are unequal -- this is not a match.
            return false;
        }

        if (methodIsDeclaredWithVariadicParameter) {
            // If the method declaration we're considering has a variadic parameter,
            // attempt to convert the given list of arguments to fit this pattern
            // e.g. foo(String s, String... s2) {} --- consider the first argument, then group the remainder as an array

            ResolvedType expectedVariadicParameterType = methodDeclaration.getLastParam().getType();
            for (ResolvedTypeParameterDeclaration tp : methodDeclaration.getTypeParameters()) {
                expectedVariadicParameterType = replaceTypeParam(expectedVariadicParameterType, tp, typeSolver);
            }

            if(countOfNeedleArgumentsPassed <= (countOfMethodParametersDeclared - 2)) {
                // If it is variadic, and the number of arguments are short by **two or more** -- this is not a match.
                // Note that omitting the variadic parameter is treated as an empty array
                //  (thus being short of only 1 argument is fine, but being short of 2 or more is not).
                return false;
            } else if (countOfNeedleArgumentsPassed == (countOfMethodParametersDeclared - 1)) {
                // If it is variadic and we are short of **exactly one** parameter, this is a match.
                // Note that omitting the variadic parameter is treated as an empty array
                //  (thus being short of only 1 argument is fine, but being short of 2 or more is not).

                // thus group the "empty" value into an empty array...
                needleArgumentTypes = groupVariadicParamValues(needleArgumentTypes, lastMethodParameterIndex, methodDeclaration.getLastParam().getType());
            } else if (countOfNeedleArgumentsPassed > countOfMethodParametersDeclared) {
                // If it is variadic, and we have an "excess" of arguments, group the "trailing" arguments into an array.
                // Confirm all of these grouped "trailing" arguments have the required type -- if not, this is not a valid type. (Maybe this is also done later..?)
                for(int variadicArgumentIndex = countOfMethodParametersDeclared; variadicArgumentIndex < countOfNeedleArgumentsPassed; variadicArgumentIndex++) {
                    ResolvedType currentArgumentType = needleArgumentTypes.get(variadicArgumentIndex);
                    boolean argumentIsAssignableToVariadicComponentType = expectedVariadicParameterType.asArrayType().getComponentType().isAssignableBy(currentArgumentType);
                    if(!argumentIsAssignableToVariadicComponentType) {
                        // If any of the arguments are not assignable to the expected variadic type, this is not a match.
                        return false;
                    }
                }
                needleArgumentTypes = groupVariadicParamValues(needleArgumentTypes, lastMethodParameterIndex, methodDeclaration.getLastParam().getType());
            } else if (countOfNeedleArgumentsPassed == countOfMethodParametersDeclared) {
                ResolvedType actualArgumentType = needleArgumentTypes.get(lastNeedleArgumentIndex);
                boolean finalArgumentIsArray = actualArgumentType.isArray() && expectedVariadicParameterType.isAssignableBy(actualArgumentType.asArrayType().getComponentType());
                if(finalArgumentIsArray) {
                    // Treat as an array of values -- in which case the expected parameter type is the common type of this array.
                    // no need to do anything
//                    expectedVariadicParameterType = actualArgumentType.asArrayType().getComponentType();
                } else {
                    // Treat as a single value -- in which case, the expected parameter type is the same as the single value.
                    needleArgumentTypes = groupVariadicParamValues(needleArgumentTypes, lastMethodParameterIndex, methodDeclaration.getLastParam().getType());
                }
            } else {
                // Should be unreachable.
            }
        }


        // The index of the final argument passed (on the method usage).
        int countOfNeedleArgumentsPassedAfterGrouping = needleArgumentTypes.size();
        int lastNeedleArgumentIndexAfterGrouping = Math.max(0, countOfNeedleArgumentsPassed - 1);

        // If variadic parameters are possible then they will have been "grouped" into a single argument.
        // At this point, therefore, the number of arguments must be equal -- if they're not, then there is no match.
        if (countOfNeedleArgumentsPassedAfterGrouping != countOfMethodParametersDeclared) {
            return false;
        }


        Map<String, ResolvedType> matchedParameters = new HashMap<>();
        boolean needForWildCardTolerance = false;
        for (int i = 0; i < countOfMethodParametersDeclared; i++) {
            ResolvedType expectedDeclaredType = methodDeclaration.getParam(i).getType();
            ResolvedType actualArgumentType = needleArgumentTypes.get(i);
            if ((expectedDeclaredType.isTypeVariable() && !(expectedDeclaredType.isWildcard())) && expectedDeclaredType.asTypeParameter().declaredOnMethod()) {
                matchedParameters.put(expectedDeclaredType.asTypeParameter().getName(), actualArgumentType);
                continue;
            }

            boolean isAssignableWithoutSubstitution = expectedDeclaredType.isAssignableBy(actualArgumentType) ||
                    (methodDeclaration.getParam(i).isVariadic() && new ResolvedArrayType(expectedDeclaredType).isAssignableBy(actualArgumentType));

            if (!isAssignableWithoutSubstitution && expectedDeclaredType.isReferenceType() && actualArgumentType.isReferenceType()) {
                isAssignableWithoutSubstitution = isAssignableMatchTypeParameters(
                        expectedDeclaredType.asReferenceType(),
                        actualArgumentType.asReferenceType(),
                        matchedParameters);
            }
            if (!isAssignableWithoutSubstitution) {
                List<ResolvedTypeParameterDeclaration> typeParameters = methodDeclaration.getTypeParameters();
                typeParameters.addAll(methodDeclaration.declaringType().getTypeParameters());
                for (ResolvedTypeParameterDeclaration tp : typeParameters) {
                    expectedDeclaredType = replaceTypeParam(expectedDeclaredType, tp, typeSolver);
                }

                if (!expectedDeclaredType.isAssignableBy(actualArgumentType)) {
                    if (actualArgumentType.isWildcard() && withWildcardTolerance && !expectedDeclaredType.isPrimitive()) {
                        needForWildCardTolerance = true;
                        continue;
                    }
                    if (methodIsDeclaredWithVariadicParameter && i == countOfMethodParametersDeclared - 1) {
                        if (new ResolvedArrayType(expectedDeclaredType).isAssignableBy(actualArgumentType)) {
                            continue;
                        }
                    }
                    return false;
                }
            }
        }
        return !withWildcardTolerance || needForWildCardTolerance;
    }

    public static boolean isAssignableMatchTypeParameters(ResolvedType expected, ResolvedType actual,
                                                          Map<String, ResolvedType> matchedParameters) {
        if (expected.isReferenceType() && actual.isReferenceType()) {
            return isAssignableMatchTypeParameters(expected.asReferenceType(), actual.asReferenceType(), matchedParameters);
        } else if (expected.isTypeVariable()) {
            matchedParameters.put(expected.asTypeParameter().getName(), actual);
            return true;
        } else if (expected.isArray()) {
            matchedParameters.put(expected.asArrayType().getComponentType().toString(), actual);
            return true;
        } else {
            throw new UnsupportedOperationException(expected.getClass().getCanonicalName() + " " + actual.getClass().getCanonicalName());
        }
    }

    public static boolean isAssignableMatchTypeParameters(ResolvedReferenceType expected, ResolvedReferenceType actual,
                                                          Map<String, ResolvedType> matchedParameters) {
        if (actual.getQualifiedName().equals(expected.getQualifiedName())) {
            return isAssignableMatchTypeParametersMatchingQName(expected, actual, matchedParameters);
        } else {
            List<ResolvedReferenceType> ancestors = actual.getAllAncestors();
            for (ResolvedReferenceType ancestor : ancestors) {
                if (isAssignableMatchTypeParametersMatchingQName(expected, ancestor, matchedParameters)) {
                    return true;
                }
            }
        }
        return false;
    }

    private static boolean isAssignableMatchTypeParametersMatchingQName(ResolvedReferenceType expected, ResolvedReferenceType actual,
                                                                        Map<String, ResolvedType> matchedParameters) {

        if (!expected.getQualifiedName().equals(actual.getQualifiedName())) {
            return false;
        }
        if (expected.typeParametersValues().size() != actual.typeParametersValues().size()) {
            throw new UnsupportedOperationException();
            //return true;
        }
        for (int i = 0; i < expected.typeParametersValues().size(); i++) {
            ResolvedType expectedParam = expected.typeParametersValues().get(i);
            ResolvedType actualParam = actual.typeParametersValues().get(i);

            // In the case of nested parameterizations eg. List<R> <-> List<Integer>
            // we should peel off one layer and ensure R <-> Integer
            if (expectedParam.isReferenceType() && actualParam.isReferenceType()) {
                ResolvedReferenceType r1 = expectedParam.asReferenceType();
                ResolvedReferenceType r2 = actualParam.asReferenceType();
                // we can have r1=A and r2=A.B (with B extends A and B is an inner class of A)
                // in this case we want to verify expected parameter from the actual parameter ancestors 
                return isAssignableMatchTypeParameters(r1, r2, matchedParameters);
            }

            if (expectedParam.isTypeVariable()) {
                String expectedParamName = expectedParam.asTypeParameter().getName();
                if (!actualParam.isTypeVariable() || !actualParam.asTypeParameter().getName().equals(expectedParamName)) {
                    return matchTypeVariable(expectedParam.asTypeVariable(), actualParam, matchedParameters);
                }
            } else if (expectedParam.isReferenceType()) {
                if (actualParam.isTypeVariable()) {
                    return matchTypeVariable(actualParam.asTypeVariable(), expectedParam, matchedParameters);
                } else if (!expectedParam.equals(actualParam)) {
                    return false;
                }
            } else if (expectedParam.isWildcard()) {
                if (expectedParam.asWildcard().isExtends()) {
                    return isAssignableMatchTypeParameters(expectedParam.asWildcard().getBoundedType(), actual, matchedParameters);
                }
                // TODO verify super bound
                return true;
            } else {
                throw new UnsupportedOperationException(expectedParam.describe());
            }
        }
        return true;
    }

    private static boolean matchTypeVariable(ResolvedTypeVariable typeVariable, ResolvedType type, Map<String, ResolvedType> matchedParameters) {
        String typeParameterName = typeVariable.asTypeParameter().getName();
        if (matchedParameters.containsKey(typeParameterName)) {
            ResolvedType matchedParameter = matchedParameters.get(typeParameterName);
            if (matchedParameter.isAssignableBy(type)) {
                return true;
            } else if (type.isAssignableBy(matchedParameter)) {
                // update matchedParameters to contain the more general type
                matchedParameters.put(typeParameterName, type);
                return true;
            }
            return false;
        } else {
            matchedParameters.put(typeParameterName, type);
        }
        return true;
    }

    public static ResolvedType replaceTypeParam(ResolvedType type, ResolvedTypeParameterDeclaration tp, TypeSolver typeSolver) {
        if (type.isTypeVariable() || type.isWildcard()) {
            if (type.describe().equals(tp.getName())) {
                List<ResolvedTypeParameterDeclaration.Bound> bounds = tp.getBounds();
                if (bounds.size() > 1) {
                    throw new UnsupportedOperationException();
                } else if (bounds.size() == 1) {
                    return bounds.get(0).getType();
                } else {
                    return new ReferenceTypeImpl(typeSolver.solveType(Object.class.getCanonicalName()), typeSolver);
                }
            }
            return type;
        } else if (type.isPrimitive()) {
            return type;
        } else if (type.isArray()) {
            return new ResolvedArrayType(replaceTypeParam(type.asArrayType().getComponentType(), tp, typeSolver));
        } else if (type.isReferenceType()) {
            ResolvedReferenceType result = type.asReferenceType();
            result = result.transformTypeParameters(typeParam -> replaceTypeParam(typeParam, tp, typeSolver)).asReferenceType();
            return result;
        } else {
            throw new UnsupportedOperationException("Replacing " + type + ", param " + tp + " with " + type.getClass().getCanonicalName());
        }
    }

    /**
     * Note the specific naming here -- parameters are part of the method declaration,
     * while arguments are the values passed when calling a method.
     * Note that "needle" refers to that value being used as a search/query term to match against.
     *
     * @return true, if the given MethodUsage matches the given name/types (normally obtained from a ResolvedMethodDeclaration)
     *
     * @see {@link MethodResolutionLogic#isApplicable(ResolvedMethodDeclaration, String, List, TypeSolver)}  }
     * @see {@link MethodResolutionLogic#isApplicable(ResolvedMethodDeclaration, String, List, TypeSolver, boolean)}
     */
    public static boolean isApplicable(MethodUsage methodUsage, String needleName, List<ResolvedType> needleParameterTypes, TypeSolver typeSolver) {
        if (!methodUsage.getName().equals(needleName)) {
            return false;
        }

        // The index of the final method parameter (on the method declaration).
        int countOfMethodUsageArgumentsPassed = methodUsage.getNoParams();
        int lastMethodUsageArgumentIndex = Math.max(0, countOfMethodUsageArgumentsPassed - 1);

        // The index of the final argument passed (on the method usage).
        int needleParameterCount = needleParameterTypes.size();
        int lastNeedleParameterIndex = Math.max(0, needleParameterCount - 1);

        // TODO: Does the method usage have a declaration at this point..?
        boolean methodIsDeclaredWithVariadicParameter = methodUsage.getDeclaration().hasVariadicParameter();

        // If the counts do not match and the method is not variadic, this is not a match.
        if (!methodIsDeclaredWithVariadicParameter && !(needleParameterCount == countOfMethodUsageArgumentsPassed)) {
            return false;
        }

        // If the counts do not match and we have provided too few arguments, this is not a match. Note that variadic parameters
        // allow you to omit the vararg, which would allow a difference of one, but a difference in count of 2 or more is not a match.
        if (!(needleParameterCount == countOfMethodUsageArgumentsPassed) && needleParameterCount < lastMethodUsageArgumentIndex) {
            return false;
        }

        // Iterate over the arguments given to the method, and compare their types against the given method's declared parameter types
        for (int i = 0; i < needleParameterCount; i++) {
            ResolvedType actualArgumentType = needleParameterTypes.get(i);

            ResolvedType expectedArgumentType;
            boolean reachedVariadicParam = methodIsDeclaredWithVariadicParameter && i >= lastMethodUsageArgumentIndex;
            if (!reachedVariadicParam) {
                // Not yet reached the variadic parameters -- the expected type is just whatever is at that position.
                expectedArgumentType = methodUsage.getParamType(i);
            } else {
                // We have reached the variadic parameters -- the expected type is the type of the last declared parameter.
                expectedArgumentType = methodUsage.getParamType(lastMethodUsageArgumentIndex);
                // Note that the given variadic value might be an array - if so, use the array's component type rather.
                // This is only valid if ONE argument has been given to the vararg parameter.
                // Example: {@code void test(String... s) {}} and {@code test(stringArray)} -- {@code String... is assignable by stringArray}
                // Example: {@code void test(String[]... s) {}} and {@code test(stringArrayArray)} -- {@code String[]... is assignable by stringArrayArray}
                boolean argumentIsArray = (needleParameterCount == countOfMethodUsageArgumentsPassed) && expectedArgumentType.isAssignableBy(actualArgumentType);
                if (!argumentIsArray) {
                    // Get the component type of the declared parameter type.
                    expectedArgumentType = expectedArgumentType.asArrayType().getComponentType();
                }
            }

            // Consider type parameters directly on the method declaration, and ALSO on the enclosing type (e.g. a class)
            List<ResolvedTypeParameterDeclaration> typeParameters = methodUsage.getDeclaration().getTypeParameters();
            typeParameters.addAll(methodUsage.declaringType().getTypeParameters());

            ResolvedType expectedTypeWithoutSubstitutions = expectedArgumentType;
            ResolvedType expectedTypeWithInference = expectedArgumentType;
            Map<ResolvedTypeParameterDeclaration, ResolvedType> derivedValues = new HashMap<>();

            // For each declared parameter, infer the types that will replace generics (type parameters)
            for (int j = 0; j < countOfMethodUsageArgumentsPassed; j++) {
                ResolvedParameterDeclaration parameter = methodUsage.getDeclaration().getParam(j);
                ResolvedType parameterType = parameter.getType();
                if (parameter.isVariadic()) {
                    // Don't continue if a vararg parameter is reached and there are no arguments left
                    if (needleParameterCount == j) {
                        break;
                    }
                    parameterType = parameterType.asArrayType().getComponentType();
                }
                inferTypes(needleParameterTypes.get(j), parameterType, derivedValues);
            }

            for (Map.Entry<ResolvedTypeParameterDeclaration, ResolvedType> entry : derivedValues.entrySet()) {
                ResolvedTypeParameterDeclaration tp = entry.getKey();
                expectedTypeWithInference = expectedTypeWithInference.replaceTypeVariables(tp, entry.getValue());
            }

            // Consider cases where type variables can be replaced (e.g. add(E element) vs add(String element))
            for (ResolvedTypeParameterDeclaration tp : typeParameters) {
                if (tp.getBounds().isEmpty()) {
                    //expectedArgumentType = expectedArgumentType.replaceTypeVariables(tp.getName(), new ReferenceTypeUsageImpl(typeSolver.solveType(Object.class.getCanonicalName()), typeSolver));
                    expectedArgumentType = expectedArgumentType.replaceTypeVariables(tp, ResolvedWildcard.extendsBound(new ReferenceTypeImpl(typeSolver.solveType(Object.class.getCanonicalName()), typeSolver)));
                } else if (tp.getBounds().size() == 1) {
                    ResolvedTypeParameterDeclaration.Bound bound = tp.getBounds().get(0);
                    if (bound.isExtends()) {
                        //expectedArgumentType = expectedArgumentType.replaceTypeVariables(tp.getName(), bound.getType());
                        expectedArgumentType = expectedArgumentType.replaceTypeVariables(tp, ResolvedWildcard.extendsBound(bound.getType()));
                    } else {
                        //expectedArgumentType = expectedArgumentType.replaceTypeVariables(tp.getName(), new ReferenceTypeUsageImpl(typeSolver.solveType(Object.class.getCanonicalName()), typeSolver));
                        expectedArgumentType = expectedArgumentType.replaceTypeVariables(tp, ResolvedWildcard.superBound(bound.getType()));
                    }
                } else {
                    throw new UnsupportedOperationException();
                }
            }

            // Consider cases where type variables involve bounds e.g. super/extends
            ResolvedType expectedTypeWithSubstitutions = expectedTypeWithoutSubstitutions;
            for (ResolvedTypeParameterDeclaration tp : typeParameters) {
                if (tp.getBounds().isEmpty()) {
                    expectedTypeWithSubstitutions = expectedTypeWithSubstitutions.replaceTypeVariables(tp, new ReferenceTypeImpl(typeSolver.solveType(Object.class.getCanonicalName()), typeSolver));
                } else if (tp.getBounds().size() == 1) {
                    ResolvedTypeParameterDeclaration.Bound bound = tp.getBounds().get(0);
                    if (bound.isExtends()) {
                        expectedTypeWithSubstitutions = expectedTypeWithSubstitutions.replaceTypeVariables(tp, bound.getType());
                    } else {
                        expectedTypeWithSubstitutions = expectedTypeWithSubstitutions.replaceTypeVariables(tp, new ReferenceTypeImpl(typeSolver.solveType(Object.class.getCanonicalName()), typeSolver));
                    }
                } else {
                    throw new UnsupportedOperationException();
                }
            }

            // If the given argument still isn't applicable even after considering type arguments/generics, this is not a match.
            if (!expectedArgumentType.isAssignableBy(actualArgumentType)
                    && !expectedTypeWithSubstitutions.isAssignableBy(actualArgumentType)
                    && !expectedTypeWithInference.isAssignableBy(actualArgumentType)
                    && !expectedTypeWithoutSubstitutions.isAssignableBy(actualArgumentType)) {
                return false;
            }
        }

        // If the checks above haven't failed, then we've found a match.
        return true;
    }

    /**
     * Filters by given function {@param keyExtractor} using a stateful filter mechanism.
     *
     * <pre>
     *      persons.stream().filter(distinctByKey(Person::getName))
     * </pre>
     * <p>
     * The example above would return a distinct list of persons containing only one person per name.
     */
    private static <T> Predicate<T> distinctByKey(Function<? super T, ?> keyExtractor) {
        Set<Object> seen = ConcurrentHashMap.newKeySet();
        return t -> seen.add(keyExtractor.apply(t));
    }

    /**
     * @param methods we expect the methods to be ordered such that inherited methods are later in the list
     */
    public static SymbolReference<ResolvedMethodDeclaration> findMostApplicable(List<ResolvedMethodDeclaration> methods,
                                                                                String name, List<ResolvedType> argumentsTypes, TypeSolver typeSolver) {
        SymbolReference<ResolvedMethodDeclaration> res = findMostApplicable(methods, name, argumentsTypes, typeSolver, false);
        if (res.isSolved()) {
            return res;
        }
        return findMostApplicable(methods, name, argumentsTypes, typeSolver, true);
    }

    public static SymbolReference<ResolvedMethodDeclaration> findMostApplicable(List<ResolvedMethodDeclaration> methods,
                                                                                String name, List<ResolvedType> argumentsTypes,
                                                                                TypeSolver typeSolver,
                                                                                boolean wildcardTolerance
    ) {

        List<ResolvedMethodDeclaration> applicableMethods = methods.stream()
                // Only consider methods with a matching name
                .filter(m -> m.getName().equals(name))
                // Filters out duplicate ResolvedMethodDeclaration by their signature.
                .filter(distinctByKey(ResolvedMethodDeclaration::getQualifiedSignature))
                // Checks if ResolvedMethodDeclaration is applicable to argumentsTypes.
                .filter((m) -> isApplicable(m, name, argumentsTypes, typeSolver, wildcardTolerance))
                .collect(Collectors.toList());

        // If no applicable methods found, return as unsolved.
        if (applicableMethods.isEmpty()) {
            return SymbolReference.unsolved(ResolvedMethodDeclaration.class);
        }

        // If there are multiple possible methods found, null arguments can help to eliminate some matches.
        if (applicableMethods.size() > 1) {
            List<Integer> nullParamIndexes = new ArrayList<>();
            for (int i = 0; i < argumentsTypes.size(); i++) {
                if (argumentsTypes.get(i).isNull()) {
                    nullParamIndexes.add(i);
                }
            }

            // If some null arguments have been provided, use this to eliminate some opitons.
            if (!nullParamIndexes.isEmpty()) {
                // remove method with array param if a non array exists and arg is null
                Set<ResolvedMethodDeclaration> removeCandidates = new HashSet<>();
                for (Integer nullParamIndex : nullParamIndexes) {
                    for (ResolvedMethodDeclaration methDecl : applicableMethods) {
                        if (methDecl.getParam(nullParamIndex).getType().isArray()) {
                            removeCandidates.add(methDecl);
                        }
                    }
                }

                // Where candidiates for removal are found, remove them.
                if (!removeCandidates.isEmpty() && removeCandidates.size() < applicableMethods.size()) {
                    applicableMethods.removeAll(removeCandidates);
                }
            }
        }

        // If only one applicable method found, short-circuit and return it here.
        if (applicableMethods.size() == 1) {
            return SymbolReference.solved(applicableMethods.get(0));
        }

        // Examine the applicable methods found, and evaluate each to determine the "best" one
        ResolvedMethodDeclaration winningCandidate = applicableMethods.get(0);
        ResolvedMethodDeclaration other = null;
        boolean possibleAmbiguity = false;
        for (int i = 1; i < applicableMethods.size(); i++) {
            other = applicableMethods.get(i);
            if (isMoreSpecific(winningCandidate, other, argumentsTypes)) {
                possibleAmbiguity = false;
            } else if (isMoreSpecific(other, winningCandidate, argumentsTypes)) {
                possibleAmbiguity = false;
                winningCandidate = other;
            } else {
                if (winningCandidate.declaringType().getQualifiedName().equals(other.declaringType().getQualifiedName())) {
                    possibleAmbiguity = true;
                } else {
                    // we expect the methods to be ordered such that inherited methods are later in the list
                }
            }
        }

        if (possibleAmbiguity) {
            // pick the first exact match if it exists
            if (!isExactMatch(winningCandidate, argumentsTypes)) {
                if (isExactMatch(other, argumentsTypes)) {
                    winningCandidate = other;
                } else {
                    throw new MethodAmbiguityException("Ambiguous method call: cannot find a most applicable method: " + winningCandidate + ", " + other);
                }
            }
        }

        return SymbolReference.solved(winningCandidate);
    }

    protected static boolean isExactMatch(ResolvedMethodLikeDeclaration method, List<ResolvedType> argumentsTypes) {
        for (int i = 0; i < method.getNumberOfParams(); i++) {
            if (!method.getParam(i).getType().equals(argumentsTypes.get(i))) {
                return false;
            }
        }
        return true;
    }

    private static ResolvedType getMethodsExplicitAndVariadicParameterType(ResolvedMethodDeclaration method, int i) {
        int numberOfParams = method.getNumberOfParams();

        if (i < numberOfParams) {
            return method.getParam(i).getType();
        } else if (method.hasVariadicParameter()) {
            return method.getParam(numberOfParams - 1).getType();
        } else {
            return null;
        }
    }

    private static boolean isMoreSpecific(ResolvedMethodDeclaration methodA, ResolvedMethodDeclaration methodB,
                                          List<ResolvedType> argumentTypes) {

        final boolean aVariadic = methodA.hasVariadicParameter();
        final boolean bVariadic = methodB.hasVariadicParameter();
        final int aNumberOfParams = methodA.getNumberOfParams();
        final int bNumberOfParams = methodB.getNumberOfParams();
        final int numberOfArgs = argumentTypes.size();
        final ResolvedType lastArgType = numberOfArgs > 0 ? argumentTypes.get(numberOfArgs - 1) : null;
        final boolean isLastArgArray = lastArgType != null && lastArgType.isArray();

        // If one method declaration has exactly the correct amount of parameters and is not variadic then it is always
        // preferred to a declaration that is variadic (and hence possibly also has a different amount of parameters).
        if (!aVariadic && aNumberOfParams == numberOfArgs && (bVariadic && (bNumberOfParams != numberOfArgs ||
                !isLastArgArray))) {
            return true;
        } else if (!bVariadic && bNumberOfParams == numberOfArgs && (aVariadic && (aNumberOfParams != numberOfArgs ||
                !isLastArgArray))) {
            return false;
        }

        // Either both methods are variadic or neither is. So we must compare the parameter types.
        for (int i = 0; i < numberOfArgs; i++) {
            ResolvedType paramTypeA = getMethodsExplicitAndVariadicParameterType(methodA, i);
            ResolvedType paramTypeB = getMethodsExplicitAndVariadicParameterType(methodB, i);
            ResolvedType argType = argumentTypes.get(i);

            // Safety: if a type is null it means a signature with too few parameters managed to get to this point.
            // This should not happen but it also means that this signature is immediately disqualified.
            if (paramTypeA == null) {
                return false;
            } else if (paramTypeB == null) {
                return true;
            }
            // Widening primitive conversions have priority over boxing/unboxing conversions when finding the most
            // applicable method. E.g. assume we have method call foo(1) and declarations foo(long) and foo(Integer).
            // The method call will call foo(long), as it requires a widening primitive conversion from int to long
            // instead of a boxing conversion from int to Integer. See JLS §15.12.2.
            // This is what we check here.
            else if (paramTypeA.isPrimitive() == argType.isPrimitive() &&
                    paramTypeB.isPrimitive() != argType.isPrimitive() &&
                    paramTypeA.isAssignableBy(argType)) {

                return true;
            } else if (paramTypeB.isPrimitive() == argType.isPrimitive() &&
                    paramTypeA.isPrimitive() != argType.isPrimitive() &&
                    paramTypeB.isAssignableBy(argType)) {

                return false;
            // if paramA and paramB are not the last parameters
            // and the type of paramA or paramB (which are not more specific at this stage) is java.lang.Object
            // then we have to consider others parameters before concluding
            } else if ((i < numberOfArgs - 1)
                    && (paramTypeB.isReferenceType() && paramTypeB.asReferenceType().getQualifiedName().equals("java.lang.Object")
                    || (paramTypeA.isReferenceType() && paramTypeA.asReferenceType().getQualifiedName().equals("java.lang.Object")))) {
                // consider others parameters
            }
            // If we get to this point then we check whether one of the methods contains a parameter type that is more
            // specific. If it does, we can assume the entire declaration is more specific as we would otherwise have
            // a situation where the declarations are ambiguous in the given context.
            else {
                boolean aAssignableFromB = paramTypeA.isAssignableBy(paramTypeB);
                boolean bAssignableFromA = paramTypeB.isAssignableBy(paramTypeA);

                if (bAssignableFromA && !aAssignableFromB) {
                    // A's parameter is more specific
                    return true;
                } else if (aAssignableFromB && !bAssignableFromA) {
                    // B's parameter is more specific
                    return false;
                }
            }
        }

        if (aVariadic && !bVariadic) {
            // if the last argument is an array then m1 is more specific
            return isLastArgArray;
        } else if (!aVariadic && bVariadic) {
            // if the last argument is an array and m1 is not variadic then
            // it is not more specific
            return !isLastArgArray;
        }

        return false;
    }

    private static boolean isMoreSpecific(MethodUsage methodA, MethodUsage methodB) {
        boolean oneMoreSpecificFound = false;
        for (int i = 0; i < methodA.getNoParams(); i++) {
            ResolvedType tdA = methodA.getParamType(i);
            ResolvedType tdB = methodB.getParamType(i);

            boolean aIsAssignableByB = tdA.isAssignableBy(tdB);
            boolean bIsAssignableByA = tdB.isAssignableBy(tdA);

            // A is more specific
            if (bIsAssignableByA && !aIsAssignableByB) {
                oneMoreSpecificFound = true;
            }
            // B is more specific
            if (aIsAssignableByB && !bIsAssignableByA) {
                return false;
            }

            // If B is vararg and A is not, A is more specific
            if (tdB.isArray() && tdB.asArrayType().getComponentType().isAssignableBy(tdA)) {
                oneMoreSpecificFound = true;
            }
        }
        return oneMoreSpecificFound;
    }

    public static Optional<MethodUsage> findMostApplicableUsage(List<MethodUsage> methods, String name, List<ResolvedType> argumentsTypes, TypeSolver typeSolver) {
        List<MethodUsage> applicableMethods = methods.stream().filter((m) -> isApplicable(m, name, argumentsTypes, typeSolver)).collect(Collectors.toList());

        if (applicableMethods.isEmpty()) {
            return Optional.empty();
        }
        if (applicableMethods.size() == 1) {
            return Optional.of(applicableMethods.get(0));
        } else {
            MethodUsage winningCandidate = applicableMethods.get(0);
            for (int i = 1; i < applicableMethods.size(); i++) {
                MethodUsage other = applicableMethods.get(i);
                if (isMoreSpecific(winningCandidate, other)) {
                    // nothing to do
                } else if (isMoreSpecific(other, winningCandidate)) {
                    winningCandidate = other;
                } else {
                    if (winningCandidate.declaringType().getQualifiedName().equals(other.declaringType().getQualifiedName())) {
                        if (!areOverride(winningCandidate, other)) {
                            throw new MethodAmbiguityException("Ambiguous method call: cannot find a most applicable method: " + winningCandidate + ", " + other + ". First declared in " + winningCandidate.declaringType().getQualifiedName());
                        }
                    } else {
                        // we expect the methods to be ordered such that inherited methods are later in the list
                        //throw new UnsupportedOperationException();
                    }
                }
            }
            return Optional.of(winningCandidate);
        }
    }

    private static boolean areOverride(MethodUsage winningCandidate, MethodUsage other) {
        if (!winningCandidate.getName().equals(other.getName())) {
            return false;
        }
        if (winningCandidate.getNoParams() != other.getNoParams()) {
            return false;
        }
        for (int i = 0; i < winningCandidate.getNoParams(); i++) {
            if (!winningCandidate.getParamTypes().get(i).equals(other.getParamTypes().get(i))) {
                return false;
            }
        }
        return true;
    }

    public static SymbolReference<ResolvedMethodDeclaration> solveMethodInType(ResolvedTypeDeclaration typeDeclaration,
                                                                               String name,
                                                                               List<ResolvedType> argumentsTypes) {
        return solveMethodInType(typeDeclaration, name, argumentsTypes, false);
    }

    // TODO: Replace TypeDeclaration.solveMethod
    public static SymbolReference<ResolvedMethodDeclaration> solveMethodInType(ResolvedTypeDeclaration typeDeclaration,
                                                                               String name,
                                                                               List<ResolvedType> argumentsTypes,
                                                                               boolean staticOnly) {

        if (typeDeclaration instanceof MethodResolutionCapability) {
            return ((MethodResolutionCapability) typeDeclaration).solveMethod(name, argumentsTypes,
                    staticOnly);
        } else {
            throw new UnsupportedOperationException(typeDeclaration.getClass().getCanonicalName());
        }
    }

    private static void inferTypes(ResolvedType source, ResolvedType target, Map<ResolvedTypeParameterDeclaration, ResolvedType> mappings) {
        if (source.equals(target)) {
            return;
        }
        if (source.isReferenceType() && target.isReferenceType()) {
            ResolvedReferenceType sourceRefType = source.asReferenceType();
            ResolvedReferenceType targetRefType = target.asReferenceType();
            if (sourceRefType.getQualifiedName().equals(targetRefType.getQualifiedName())) {
                if (!sourceRefType.isRawType() && !targetRefType.isRawType()) {
                    for (int i = 0; i < sourceRefType.typeParametersValues().size(); i++) {
                        inferTypes(sourceRefType.typeParametersValues().get(i), targetRefType.typeParametersValues().get(i), mappings);
                    }
                }
            }
            return;
        }
        if (source.isReferenceType() && target.isWildcard()) {
            if (target.asWildcard().isBounded()) {
                inferTypes(source, target.asWildcard().getBoundedType(), mappings);
                return;
            }
            return;
        }
        if (source.isWildcard() && target.isWildcard()) {
            return;
        }
        if (source.isReferenceType() && target.isTypeVariable()) {
            mappings.put(target.asTypeParameter(), source);
            return;
        }

        if (source.isWildcard() && target.isReferenceType()) {
            if (source.asWildcard().isBounded()) {
                inferTypes(source.asWildcard().getBoundedType(), target, mappings);
            }
            return;
        }

        if (source.isWildcard() && target.isTypeVariable()) {
            mappings.put(target.asTypeParameter(), source);
            return;
        }
        if (source.isTypeVariable() && target.isTypeVariable()) {
            mappings.put(target.asTypeParameter(), source);
            return;
        }
        if (source.isPrimitive() || target.isPrimitive()) {
            return;
        }
        if (source.isNull()) {
            return;
        }
    }


}
