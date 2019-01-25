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

package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.resolution.MethodAmbiguityException;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.types.*;
import com.github.javaparser.symbolsolver.logic.MethodResolutionCapability;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;

import java.util.*;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;

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

    private static boolean isApplicable(ResolvedMethodDeclaration method, String name, List<ResolvedType> argumentsTypes, TypeSolver typeSolver, boolean withWildcardTolerance) {
        if (!method.getName().equals(name)) {
            return false;
        }
        if (method.hasVariadicParameter()) {
            int pos = method.getNumberOfParams() - 1;
            if (method.getNumberOfParams() == argumentsTypes.size()) {
                // check if the last value is directly assignable as an array
                ResolvedType expectedType = method.getLastParam().getType();
                ResolvedType actualType = argumentsTypes.get(pos);
                if (!expectedType.isAssignableBy(actualType)) {
                    for (ResolvedTypeParameterDeclaration tp : method.getTypeParameters()) {
                        expectedType = replaceTypeParam(expectedType, tp, typeSolver);
                    }
                    if (!expectedType.isAssignableBy(actualType)) {
                        if (actualType.isArray() && expectedType.isAssignableBy(actualType.asArrayType().getComponentType())) {
                            argumentsTypes.set(pos, actualType.asArrayType().getComponentType());
                        } else {
                            argumentsTypes = groupVariadicParamValues(argumentsTypes, pos, method.getLastParam().getType());
                        }
                    }
                } // else it is already assignable, nothing to do
            } else {
                if (pos > argumentsTypes.size()) {
                    return false;
                }
                argumentsTypes = groupVariadicParamValues(argumentsTypes, pos, method.getLastParam().getType());
            }
        }

        if (method.getNumberOfParams() != argumentsTypes.size()) {
            return false;
        }
        Map<String, ResolvedType> matchedParameters = new HashMap<>();
        boolean needForWildCardTolerance = false;
        for (int i = 0; i < method.getNumberOfParams(); i++) {
            ResolvedType expectedType = method.getParam(i).getType();
            ResolvedType actualType = argumentsTypes.get(i);
            if ((expectedType.isTypeVariable() && !(expectedType.isWildcard())) && expectedType.asTypeParameter().declaredOnMethod()) {
                matchedParameters.put(expectedType.asTypeParameter().getName(), actualType);
                continue;
            }
            boolean isAssignableWithoutSubstitution = expectedType.isAssignableBy(actualType) ||
                    (method.getParam(i).isVariadic() && new ResolvedArrayType(expectedType).isAssignableBy(actualType));
            if (!isAssignableWithoutSubstitution && expectedType.isReferenceType() && actualType.isReferenceType()) {
                isAssignableWithoutSubstitution = isAssignableMatchTypeParameters(
                        expectedType.asReferenceType(),
                        actualType.asReferenceType(),
                        matchedParameters);
            }
            if (!isAssignableWithoutSubstitution) {
                List<ResolvedTypeParameterDeclaration> typeParameters = method.getTypeParameters();
                typeParameters.addAll(method.declaringType().getTypeParameters());
                for (ResolvedTypeParameterDeclaration tp : typeParameters) {
                    expectedType = replaceTypeParam(expectedType, tp, typeSolver);
                }

                if (!expectedType.isAssignableBy(actualType)) {
                    if (actualType.isWildcard() && withWildcardTolerance && !expectedType.isPrimitive()) {
                        needForWildCardTolerance = true;
                        continue;
                    }
                    if (method.hasVariadicParameter() && i == method.getNumberOfParams() - 1) {
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

    public static boolean isAssignableMatchTypeParameters(ResolvedType expected, ResolvedType actual,
                                                          Map<String, ResolvedType> matchedParameters) {
        if (expected.isReferenceType() && actual.isReferenceType()) {
            return isAssignableMatchTypeParameters(expected.asReferenceType(), actual.asReferenceType(), matchedParameters);
        } else if (expected.isTypeVariable()) {
            matchedParameters.put(expected.asTypeParameter().getName(), actual);
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

                return isAssignableMatchTypeParametersMatchingQName(r1, r2, matchedParameters);
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

    public static boolean isApplicable(MethodUsage method, String name, List<ResolvedType> argumentsTypes, TypeSolver typeSolver) {
        if (!method.getName().equals(name)) {
            return false;
        }
        // TODO Consider varargs
        if (method.getNoParams() != argumentsTypes.size()) {
            return false;
        }
        for (int i = 0; i < method.getNoParams(); i++) {
            ResolvedType expectedType = method.getParamType(i);
            ResolvedType expectedTypeWithoutSubstitutions = expectedType;
            ResolvedType expectedTypeWithInference = method.getParamType(i);
            ResolvedType actualType = argumentsTypes.get(i);

            List<ResolvedTypeParameterDeclaration> typeParameters = method.getDeclaration().getTypeParameters();
            typeParameters.addAll(method.declaringType().getTypeParameters());

            if (expectedType.describe().equals(actualType.describe())) {
                return true;
            }

            Map<ResolvedTypeParameterDeclaration, ResolvedType> derivedValues = new HashMap<>();
            for (int j = 0; j < method.getParamTypes().size(); j++) {
                ResolvedParameterDeclaration parameter = method.getDeclaration().getParam(i);
                ResolvedType parameterType = parameter.getType();
                if (parameter.isVariadic()) {
                    parameterType = parameterType.asArrayType().getComponentType();
                }
                inferTypes(argumentsTypes.get(j), parameterType, derivedValues);
            }

            for (Map.Entry<ResolvedTypeParameterDeclaration, ResolvedType> entry : derivedValues.entrySet()) {
                ResolvedTypeParameterDeclaration tp = entry.getKey();
                expectedTypeWithInference = expectedTypeWithInference.replaceTypeVariables(tp, entry.getValue());
            }

            for (ResolvedTypeParameterDeclaration tp : typeParameters) {
                if (tp.getBounds().isEmpty()) {
                    //expectedType = expectedType.replaceTypeVariables(tp.getName(), new ReferenceTypeUsageImpl(typeSolver.solveType(Object.class.getCanonicalName()), typeSolver));
                    expectedType = expectedType.replaceTypeVariables(tp, ResolvedWildcard.extendsBound(new ReferenceTypeImpl(typeSolver.solveType(Object.class.getCanonicalName()), typeSolver)));
                } else if (tp.getBounds().size() == 1) {
                    ResolvedTypeParameterDeclaration.Bound bound = tp.getBounds().get(0);
                    if (bound.isExtends()) {
                        //expectedType = expectedType.replaceTypeVariables(tp.getName(), bound.getType());
                        expectedType = expectedType.replaceTypeVariables(tp, ResolvedWildcard.extendsBound(bound.getType()));
                    } else {
                        //expectedType = expectedType.replaceTypeVariables(tp.getName(), new ReferenceTypeUsageImpl(typeSolver.solveType(Object.class.getCanonicalName()), typeSolver));
                        expectedType = expectedType.replaceTypeVariables(tp, ResolvedWildcard.superBound(bound.getType()));
                    }
                } else {
                    throw new UnsupportedOperationException();
                }
            }
            ResolvedType expectedType2 = expectedTypeWithoutSubstitutions;
            for (ResolvedTypeParameterDeclaration tp : typeParameters) {
                if (tp.getBounds().isEmpty()) {
                    expectedType2 = expectedType2.replaceTypeVariables(tp, new ReferenceTypeImpl(typeSolver.solveType(Object.class.getCanonicalName()), typeSolver));
                } else if (tp.getBounds().size() == 1) {
                    ResolvedTypeParameterDeclaration.Bound bound = tp.getBounds().get(0);
                    if (bound.isExtends()) {
                        expectedType2 = expectedType2.replaceTypeVariables(tp, bound.getType());
                    } else {
                        expectedType2 = expectedType2.replaceTypeVariables(tp, new ReferenceTypeImpl(typeSolver.solveType(Object.class.getCanonicalName()), typeSolver));
                    }
                } else {
                    throw new UnsupportedOperationException();
                }
            }
            if (!expectedType.isAssignableBy(actualType)
                    && !expectedType2.isAssignableBy(actualType)
                    && !expectedTypeWithInference.isAssignableBy(actualType)
                    && !expectedTypeWithoutSubstitutions.isAssignableBy(actualType)) {
                return false;
            }
        }
        return true;
    }
    
    /**
     * Filters by given function {@param keyExtractor} using a stateful filter mechanism.
     * 
     * <pre>
     *      persons.stream().filter(distinctByKey(Person::getName))
     * </pre>
     * 
     * The example above would return a distinct list of persons containing only one person per name.
     * 
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
                                                                                String name, List<ResolvedType> argumentsTypes, TypeSolver typeSolver, boolean wildcardTolerance) {
        
        List<ResolvedMethodDeclaration> methodsWithMatchingName = methods.stream()
                .filter(m -> m.getName().equals(name))
                .collect(Collectors.toList());
        
        List<ResolvedMethodDeclaration> applicableMethods = methodsWithMatchingName.stream()
                // Filters out duplicate ResolvedMethodDeclaration by their signature.
                .filter(distinctByKey(ResolvedMethodDeclaration::getQualifiedSignature)) 
                // Checks if ResolvedMethodDeclaration is applicable to argumentsTypes.
                .filter((m) -> isApplicable(m, name, argumentsTypes, typeSolver, wildcardTolerance))
                .collect(Collectors.toList());
        
        if (applicableMethods.isEmpty()) {
            return SymbolReference.unsolved(ResolvedMethodDeclaration.class);
        }

        if (applicableMethods.size() > 1) {
            List<Integer> nullParamIndexes = new ArrayList<>();
            for (int i = 0; i < argumentsTypes.size(); i++) {
                if (argumentsTypes.get(i).isNull()) {
                    nullParamIndexes.add(i);
                }
            }
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
                if (!removeCandidates.isEmpty() && removeCandidates.size() < applicableMethods.size()) {
                    applicableMethods.removeAll(removeCandidates);
                }
            }
        }
        if (applicableMethods.size() == 1) {
            return SymbolReference.solved(applicableMethods.get(0));
        } else {
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
        for (int i = 0 ; i < numberOfArgs ; i++) {
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
            }
            // If we get to this point then we check whether one of the methods contains a parameter type that is more
            // specific. If it does, we can assume the entire declaration is more specific as we would otherwise have
            // a situation where the declarations are ambiguous in the given context.
            else {
                boolean aAssignableFromB = paramTypeA.isAssignableBy(paramTypeB);
                boolean bAssignableFromA = paramTypeB.isAssignableBy(paramTypeA);

                if (bAssignableFromA && !aAssignableFromB){
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

            // B is more specific
            if (bIsAssignableByA && !aIsAssignableByB) {
                oneMoreSpecificFound = true;
            }
            // A is more specific
            if (aIsAssignableByB && !bIsAssignableByA) {
                return false;
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
