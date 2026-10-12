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
package com.github.javaparser.resolution.logic;

import com.github.javaparser.resolution.MethodAmbiguityException;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.model.LambdaArgumentTypePlaceholder;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.*;
import java.util.*;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;

/**
 * @author Federico Tomassetti
 */
public class MethodResolutionLogic {

    private static String JAVA_LANG_OBJECT = Object.class.getCanonicalName();

    private static List<ResolvedType> groupVariadicParamValues(
            List<ResolvedType> argumentsTypes, int startVariadic, ResolvedType variadicType) {
        List<ResolvedType> res = new ArrayList<>(argumentsTypes.subList(0, startVariadic));
        List<ResolvedType> variadicValues = argumentsTypes.subList(startVariadic, argumentsTypes.size());
        if (variadicValues.isEmpty()) {
            // TODO if there are no variadic values we should default to the bound of the formal type
            res.add(variadicType);
        } else {
            ResolvedType componentType = findCommonType(variadicValues);
            res.add(convertToVariadicParameter(componentType));
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

    public static boolean isApplicable(
            ResolvedMethodDeclaration method, String name, List<ResolvedType> argumentsTypes, TypeSolver typeSolver) {
        return isApplicable(method, name, argumentsTypes, typeSolver, false);
    }

    private static boolean isConflictingLambdaType(
            LambdaArgumentTypePlaceholder lambdaPlaceholder, ResolvedType expectedType) {
        // TODO: It might be possible to use the resolved type variable here, but that would either require
        //  a type parameters map to be passed in, or the type variable to be resolved here which could lead
        //  to duplicated work or maybe infinite recursion.
        if (!expectedType.isReferenceType()) {
            return false;
        }
        Optional<MethodUsage> maybeFunctionalInterface = FunctionalInterfaceLogic.getFunctionalMethod(expectedType);
        if (maybeFunctionalInterface.isPresent()) {
            MethodUsage functionalInterface = maybeFunctionalInterface.get();
            // If the lambda expression does not have the same number of parameters as the functional interface
            // method, the lambda cannot implement that interface.
            if (lambdaPlaceholder.getParameterCount().isPresent()
                    && functionalInterface.getNoParams()
                            != lambdaPlaceholder.getParameterCount().get()) {
                return true;
            }
            // If the lambda method has a block body then:
            //   1. If the block contains a return statement with a returned value, the lambda can only implement
            //      non-void methods.
            //   2. If the block contains an empty return statement, or no return statement, the lambda can only
            //      implement void methods.
            if (lambdaPlaceholder.bodyBlockHasExplicitNonVoidReturn().isPresent()) {
                boolean lambdaReturnIsVoid =
                        !lambdaPlaceholder.bodyBlockHasExplicitNonVoidReturn().get();
                if (lambdaReturnIsVoid && !functionalInterface.returnType().isVoid()) {
                    return true;
                }
                if (!lambdaReturnIsVoid && functionalInterface.returnType().isVoid()) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * Note the specific naming here -- parameters are part of the method declaration,
     * while arguments are the values passed when calling a method.
     * Note that "needle" refers to that value being used as a search/query term to match against.
     *
     * @return true, if the given ResolvedMethodDeclaration matches the given name/types (normally obtained from a MethodUsage)
     *
     * @see MethodResolutionLogic#isApplicable(MethodUsage, String, List, TypeSolver)
     */
    private static boolean isApplicable(
            ResolvedMethodDeclaration methodDeclaration,
            String needleName,
            List<ResolvedType> needleArgumentTypes,
            TypeSolver typeSolver,
            boolean withWildcardTolerance) {
        // Without anything known about the type the method is looked up in, the candidate is checked against its
        // declared signature, the type variables of its declaring type included.
        return isApplicable(
                methodDeclaration,
                declaredParameterTypes(methodDeclaration),
                needleName,
                needleArgumentTypes,
                typeSolver,
                withWildcardTolerance);
    }

    /**
     * Checks whether {@code methodDeclaration} can be called with {@code needleArgumentTypes}, comparing the
     * arguments with {@code parameterTypes} rather than with the declared parameter types.
     * <p>
     * The declaration still provides everything that does not depend on where the method is looked up: its name,
     * its arity, whether its last parameter is variadic and its own type parameters. Only the types the arguments
     * are compared with may differ. A type variable accepts any argument that is not itself a type variable (see
     * {@link ResolvedTypeVariable#isAssignableBy(ResolvedType)}), whereas the type argument it is replaced with
     * accepts only its subtypes: that is what makes {@code set(U)} inapplicable to an argument that is not a
     * subtype of the type bound to {@code U}.
     *
     * @param parameterTypes the types of the parameters of {@code methodDeclaration}, as seen from the type the
     *     method is looked up in: they differ from the declared ones when that type supplies type arguments for
     *     the type variables of the declaring type.
     */
    private static boolean isApplicable(
            ResolvedMethodDeclaration methodDeclaration,
            List<ResolvedType> parameterTypes,
            String needleName,
            List<ResolvedType> needleArgumentTypes,
            TypeSolver typeSolver,
            boolean withWildcardTolerance) {
        if (!methodDeclaration.getName().equals(needleName)) {
            return false;
        }
        // The index of the final method parameter (on the method declaration).
        int countOfMethodParametersDeclared = methodDeclaration.getNumberOfParams();
        // The index of the final argument passed (on the method usage).
        int countOfNeedleArgumentsPassed = needleArgumentTypes.size();
        boolean methodIsDeclaredWithVariadicParameter = methodDeclaration.hasVariadicParameter();
        if (!isArityCompatible(
                countOfMethodParametersDeclared, countOfNeedleArgumentsPassed, methodIsDeclaredWithVariadicParameter)) {
            return false;
        }
        if (methodIsDeclaredWithVariadicParameter) {
            // If the method declaration we're considering has a variadic parameter,
            // attempt to convert the given list of arguments to fit this pattern
            // e.g. foo(String s, String... s2) {} --- consider the first argument, then group the remainder as an array
            // Taken from parameterTypes, so that a variadic parameter of type T... is seen as String... on a
            // receiver that binds T to String.
            ResolvedType expectedVariadicParameterType = parameterTypes.get(countOfMethodParametersDeclared - 1);
            for (ResolvedTypeParameterDeclaration tp : methodDeclaration.getTypeParameters()) {
                expectedVariadicParameterType = replaceTypeParam(expectedVariadicParameterType, tp, typeSolver);
            }
            if (countOfNeedleArgumentsPassed > countOfMethodParametersDeclared) {
                // If it is variadic, and we have an "excess" of arguments, group the "trailing" arguments into an
                // array.
                // Confirm all of these grouped "trailing" arguments have the required type -- if not, this is not a
                // valid type. (Maybe this is also done later..?)
                for (int variadicArgumentIndex = countOfMethodParametersDeclared;
                        variadicArgumentIndex < countOfNeedleArgumentsPassed;
                        variadicArgumentIndex++) {
                    ResolvedType currentArgumentType = needleArgumentTypes.get(variadicArgumentIndex);
                    ResolvedType variadicComponentType =
                            expectedVariadicParameterType.asArrayType().getComponentType();
                    boolean argumentIsAssignableToVariadicComponentType =
                            variadicComponentType.isAssignableBy(currentArgumentType);
                    // Check boxing/unboxing for varargs
                    if (!argumentIsAssignableToVariadicComponentType) {
                        argumentIsAssignableToVariadicComponentType = isBoxingCompatibleWithTypeSolver(
                                variadicComponentType, currentArgumentType, typeSolver);
                    }
                    if (!argumentIsAssignableToVariadicComponentType) {
                        return false;
                    }
                }
            }
            needleArgumentTypes =
                    groupTrailingArgumentsIntoArray(parameterTypes, needleArgumentTypes, expectedVariadicParameterType);
        }
        // The index of the final argument passed (on the method usage).
        int countOfNeedleArgumentsPassedAfterGrouping = needleArgumentTypes.size();
        // If variadic parameters are possible then they will have been "grouped" into a single argument.
        // At this point, therefore, the number of arguments must be equal -- if they're not, then there is no match.
        if (countOfNeedleArgumentsPassedAfterGrouping != countOfMethodParametersDeclared) {
            return false;
        }
        Map<String, ResolvedType> matchedParameters = new HashMap<>();
        boolean needForWildCardTolerance = false;
        for (int i = 0; i < countOfMethodParametersDeclared; i++) {
            // The parameter type as seen from the type the method is looked up in (see parameterTypes): it is
            // what distinguishes set(T) from set(U) once T and U are bound to different types.
            ResolvedType expectedDeclaredType = parameterTypes.get(i);
            ResolvedType actualArgumentType = needleArgumentTypes.get(i);
            if (actualArgumentType instanceof LambdaArgumentTypePlaceholder
                    && isConflictingLambdaType(
                            (LambdaArgumentTypePlaceholder) actualArgumentType, expectedDeclaredType)) {
                return false;
            }
            if ((expectedDeclaredType.isTypeVariable() && !(expectedDeclaredType.isWildcard()))
                    && expectedDeclaredType.asTypeParameter().declaredOnMethod()) {
                matchedParameters.put(expectedDeclaredType.asTypeParameter().getName(), actualArgumentType);
                continue;
            }
            // if this is a variable arity method and we are trying to evaluate the last parameter
            // then we consider that an array of objects can be assigned by any array
            // for example:
            // The method call expression String.format("%d", new int[] {1})
            // must refer to the method String.format(String, Object...)
            // even if an array of primitive type cannot be assigned to an array of Object
            if (methodDeclaration.getParam(i).isVariadic()
                    && (i == countOfMethodParametersDeclared - 1)
                    && isArrayOfObject(expectedDeclaredType)
                    && actualArgumentType.isArray()) {
                continue;
            }
            boolean isAssignableWithoutSubstitution = expectedDeclaredType.isAssignableBy(actualArgumentType)
                    || (methodDeclaration.getParam(i).isVariadic()
                            && convertToVariadicParameter(expectedDeclaredType).isAssignableBy(actualArgumentType));
            if (!isAssignableWithoutSubstitution
                    && expectedDeclaredType.isReferenceType()
                    && actualArgumentType.isReferenceType()) {
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
                    // Check boxing/unboxing compatibility using TypeSolver
                    if (isBoxingCompatibleWithTypeSolver(expectedDeclaredType, actualArgumentType, typeSolver)) {
                        // This parameter is compatible via boxing/unboxing
                        continue;
                    }
                    if (actualArgumentType.isWildcard()
                            && withWildcardTolerance
                            && !expectedDeclaredType.isPrimitive()) {
                        needForWildCardTolerance = true;
                        continue;
                    }
                    // if the expected is java.lang.Math.max(double,double) and the type parameters are defined with
                    // constrain
                    // for example LambdaConstraintType{bound=TypeVariable {ReflectionTypeParameter{typeVariable=T}}},
                    // LambdaConstraintType{bound=TypeVariable {ReflectionTypeParameter{typeVariable=U}}}
                    // we want to keep this method for future resolution
                    if (actualArgumentType.isConstraint()
                            && withWildcardTolerance
                            && (actualArgumentType.asConstraintType().getBound().isTypeVariable()
                                    || (!actualArgumentType
                                                    .asConstraintType()
                                                    .getBound()
                                                    .isTypeVariable()
                                            && expectedDeclaredType.isAssignableBy(actualArgumentType
                                                    .asConstraintType()
                                                    .getBound())))) {
                        needForWildCardTolerance = true;
                        continue;
                    }
                    if (methodIsDeclaredWithVariadicParameter && i == countOfMethodParametersDeclared - 1) {
                        if (convertToVariadicParameter(expectedDeclaredType).isAssignableBy(actualArgumentType)) {
                            continue;
                        }
                        // Variadic arguments grouped into an array may match the component type through
                        // boxing, unboxing or widening (JLS 15.12.2.4), e.g. print(1, 2) with print(Integer...)
                        if (expectedDeclaredType.isArray()
                                && actualArgumentType.isArray()
                                && isBoxingCompatibleWithTypeSolver(
                                        expectedDeclaredType.asArrayType().getComponentType(),
                                        actualArgumentType.asArrayType().getComponentType(),
                                        typeSolver)) {
                            continue;
                        }
                    }
                    return false;
                }
            }
        }
        return !withWildcardTolerance || needForWildCardTolerance;
    }

    private static boolean isArrayOfObject(ResolvedType type) {
        return type.isArray()
                && type.asArrayType().getComponentType().isReferenceType()
                && type.asArrayType().getComponentType().asReferenceType().isJavaLangObject();
    }

    private static ResolvedArrayType convertToVariadicParameter(ResolvedType type) {
        return type.isArray() ? type.asArrayType() : new ResolvedArrayType(type);
    }

    /**
     * Checks whether the number of arguments passed is compatible with the number of
     * parameters declared on a method, taking variadic parameters into account.
     *
     * @param declaredCount the number of parameters declared on the method
     * @param passedCount   the number of arguments passed at the call site
     * @param isVariadic    whether the method has a variadic (varargs) last parameter
     * @return true if the arity is compatible, false otherwise
     */
    private static boolean isArityCompatible(int declaredCount, int passedCount, boolean isVariadic) {
        if (!isVariadic) {
            return passedCount == declaredCount;
        }
        // Variadic methods allow omitting the vararg (treated as empty array),
        // so being short by one is fine, but short by two or more is not.
        return passedCount >= declaredCount - 1;
    }

    /**
     * Replaces type variables in the given type using wildcard bounds derived from
     * the type parameter declarations. Unbounded type parameters are replaced with
     * {@code ? extends Object}, bounded ones with their declared bound direction.
     */
    private static ResolvedType replaceTypeVariablesWithWildcards(
            ResolvedType type, List<ResolvedTypeParameterDeclaration> typeParameters, TypeSolver typeSolver) {
        for (ResolvedTypeParameterDeclaration tp : typeParameters) {
            if (tp.getBounds().isEmpty()) {
                type = type.replaceTypeVariables(
                        tp,
                        ResolvedWildcard.extendsBound(new ReferenceTypeImpl(typeSolver.solveType(JAVA_LANG_OBJECT))));
            } else if (tp.getBounds().size() == 1) {
                ResolvedTypeParameterDeclaration.Bound bound = tp.getBounds().get(0);
                if (bound.isExtends()) {
                    type = type.replaceTypeVariables(tp, ResolvedWildcard.extendsBound(bound.getType()));
                } else {
                    type = type.replaceTypeVariables(tp, ResolvedWildcard.superBound(bound.getType()));
                }
            } else {
                throw new UnsupportedOperationException();
            }
        }
        return type;
    }

    /**
     * Replaces type variables in the given type using concrete bound types derived
     * from the type parameter declarations. Unbounded type parameters are replaced
     * with {@code Object}, bounded ones with their declared bound type directly.
     */
    private static ResolvedType replaceTypeVariablesWithBounds(
            ResolvedType type, List<ResolvedTypeParameterDeclaration> typeParameters, TypeSolver typeSolver) {
        for (ResolvedTypeParameterDeclaration tp : typeParameters) {
            if (tp.getBounds().isEmpty()) {
                type = type.replaceTypeVariables(tp, new ReferenceTypeImpl(typeSolver.solveType(JAVA_LANG_OBJECT)));
            } else if (tp.getBounds().size() == 1) {
                ResolvedTypeParameterDeclaration.Bound bound = tp.getBounds().get(0);
                if (bound.isExtends()) {
                    type = type.replaceTypeVariables(tp, bound.getType());
                } else {
                    type = type.replaceTypeVariables(tp, new ReferenceTypeImpl(typeSolver.solveType(JAVA_LANG_OBJECT)));
                }
            } else {
                throw new UnsupportedOperationException();
            }
        }
        return type;
    }

    /**
     * Returns the index of the last parameter in a parameter list.
     * Helper method to safely get the last parameter index even for empty lists.
     *
     * @param countOfMethodParametersDeclared the total number of parameters
     * @return the index of the last parameter (0-based), or 0 if there are no parameters
     */
    private static int getLastParameterIndex(int countOfMethodParametersDeclared) {
        return Math.max(0, countOfMethodParametersDeclared - 1);
    }

    /**
     * Groups the arguments passed to a variadic parameter into a single array argument, so that they can be
     * compared one to one with the parameters.
     *
     * @param parameterTypes the parameter types the arguments are compared with, the last one being the variadic
     *     parameter
     */
    private static List<ResolvedType> groupTrailingArgumentsIntoArray(
            List<ResolvedType> parameterTypes,
            List<ResolvedType> needleArgumentTypes,
            ResolvedType expectedVariadicParameterType) {
        // The index of the final method parameter (on the method declaration).
        int countOfMethodParametersDeclared = parameterTypes.size();
        int lastMethodParameterIndex = getLastParameterIndex(countOfMethodParametersDeclared);
        // The index of the final argument passed (on the method usage).
        int countOfNeedleArgumentsPassed = needleArgumentTypes.size();
        int lastNeedleArgumentIndex = getLastParameterIndex(countOfNeedleArgumentsPassed);
        if (countOfNeedleArgumentsPassed > countOfMethodParametersDeclared) {
            // If it is variadic, and we have an "excess" of arguments, group the "trailing" arguments into an array.
            // Here we are sure that all of these grouped "trailing" arguments have the required type
            needleArgumentTypes = groupVariadicParamValues(
                    needleArgumentTypes, lastMethodParameterIndex, parameterTypes.get(lastMethodParameterIndex));
        }
        if (countOfNeedleArgumentsPassed == (countOfMethodParametersDeclared - 1)) {
            // If it is variadic and we are short of **exactly one** parameter, this is a match.
            // Note that omitting the variadic parameter is treated as an empty array
            //  (thus being short of only 1 argument is fine, but being short of 2 or more is not).
            // thus group the "empty" value into an empty array...
            needleArgumentTypes = groupVariadicParamValues(
                    needleArgumentTypes, lastMethodParameterIndex, parameterTypes.get(lastMethodParameterIndex));
        } else if (countOfNeedleArgumentsPassed == countOfMethodParametersDeclared) {
            ResolvedType actualArgumentType = needleArgumentTypes.get(lastNeedleArgumentIndex);
            boolean finalArgumentIsArray = actualArgumentType.isArray()
                    && expectedVariadicParameterType.isAssignableBy(
                            actualArgumentType.asArrayType().getComponentType());
            if (finalArgumentIsArray) {
                // Treat as an array of values -- in which case the expected parameter type is the common type of this
                // array.
                // no need to do anything
                // expectedVariadicParameterType = actualArgumentType.asArrayType().getComponentType();
            } else {
                // Treat as a single value -- in which case, the expected parameter type is the same as the single
                // value.
                needleArgumentTypes = groupVariadicParamValues(
                        needleArgumentTypes, lastMethodParameterIndex, parameterTypes.get(lastMethodParameterIndex));
            }
        } else {
            // Should be unreachable.
        }
        return needleArgumentTypes;
    }

    public static boolean isAssignableMatchTypeParameters(
            ResolvedType expected, ResolvedType actual, Map<String, ResolvedType> matchedParameters) {
        if (expected.isReferenceType() && actual.isReferenceType()) {
            return isAssignableMatchTypeParameters(
                    expected.asReferenceType(), actual.asReferenceType(), matchedParameters);
        }
        if (expected.isReferenceType() && ResolvedPrimitiveType.isBoxType(expected) && actual.isPrimitive()) {
            ResolvedPrimitiveType expectedType = ResolvedPrimitiveType.byBoxTypeQName(
                            expected.asReferenceType().getQualifiedName())
                    .get()
                    .asPrimitive();
            return expected.isAssignableBy(actual);
        }
        if (expected.isTypeVariable()) {
            matchedParameters.put(expected.asTypeParameter().getName(), actual);
            return true;
        }
        if (expected.isArray()) {
            matchedParameters.put(expected.asArrayType().getComponentType().toString(), actual);
            return true;
        }
        throw new UnsupportedOperationException(
                expected.getClass().getCanonicalName() + " " + actual.getClass().getCanonicalName());
    }

    public static boolean isAssignableMatchTypeParameters(
            ResolvedReferenceType expected, ResolvedReferenceType actual, Map<String, ResolvedType> matchedParameters) {
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

    private static boolean isAssignableMatchTypeParametersMatchingQName(
            ResolvedReferenceType expected, ResolvedReferenceType actual, Map<String, ResolvedType> matchedParameters) {
        if (!expected.getQualifiedName().equals(actual.getQualifiedName())) {
            return false;
        }
        if (expected.typeParametersValues().size()
                != actual.typeParametersValues().size()) {
            throw new UnsupportedOperationException();
            // return true;
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
            if (expectedParam.isArray() && actualParam.isArray()) {
                ResolvedType r1 = expectedParam.asArrayType().getComponentType();
                ResolvedType r2 = actualParam.asArrayType().getComponentType();
                // try to verify the component type of each array
                return isAssignableMatchTypeParameters(r1, r2, matchedParameters);
            }
            if (expectedParam.isTypeVariable()) {
                String expectedParamName = expectedParam.asTypeParameter().getName();
                if (!actualParam.isTypeVariable()
                        || !actualParam.asTypeParameter().getName().equals(expectedParamName)) {
                    return matchTypeVariable(expectedParam.asTypeVariable(), actualParam, matchedParameters);
                }
                // actualParam is a TypeVariable and actualParam has the same name as expectedParamName
                // We should definitely consider that types are assignable
                return true;
            } else if (expectedParam.isReferenceType()) {
                if (actualParam.isTypeVariable()) {
                    return matchTypeVariable(actualParam.asTypeVariable(), expectedParam, matchedParameters);
                }
                if (!expectedParam.equals(actualParam)) {
                    return false;
                }
            }
            if (expectedParam.isWildcard()) {
                if (expectedParam.asWildcard().isExtends()) {
                    // trying to compare with unbounded wildcard type parameter <?>
                    if (actualParam.isWildcard() && !actualParam.asWildcard().isBounded()) {
                        return true;
                    }
                    if (actualParam.isTypeVariable()) {
                        return matchTypeVariable(
                                actualParam.asTypeVariable(),
                                expectedParam.asWildcard().getBoundedType(),
                                matchedParameters);
                    }
                    return isAssignableMatchTypeParameters(
                            expectedParam.asWildcard().getBoundedType(), actualParam, matchedParameters);
                }
                // TODO verify super bound
                return true;
            }
            throw new UnsupportedOperationException(expectedParam.describe());
        }
        return true;
    }

    private static boolean matchTypeVariable(
            ResolvedTypeVariable typeVariable, ResolvedType type, Map<String, ResolvedType> matchedParameters) {
        String typeParameterName = typeVariable.asTypeParameter().getName();
        if (matchedParameters.containsKey(typeParameterName)) {
            ResolvedType matchedParameter = matchedParameters.get(typeParameterName);
            if (matchedParameter.isAssignableBy(type)) {
                return true;
            }
            if (type.isAssignableBy(matchedParameter)) {
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

    public static ResolvedType replaceTypeParam(
            ResolvedType type, ResolvedTypeParameterDeclaration tp, TypeSolver typeSolver) {
        if (type.isTypeVariable() || type.isWildcard()) {
            if (type.describe().equals(tp.getName())) {
                List<ResolvedTypeParameterDeclaration.Bound> bounds = tp.getBounds();
                if (bounds.size() > 1) {
                    throw new UnsupportedOperationException();
                }
                if (bounds.size() == 1) {
                    return bounds.get(0).getType();
                }
                return new ReferenceTypeImpl(typeSolver.solveType(JAVA_LANG_OBJECT));
            }
            return type;
        }
        if (type.isPrimitive()) {
            return type;
        }
        if (type.isArray()) {
            return new ResolvedArrayType(replaceTypeParam(type.asArrayType().getComponentType(), tp, typeSolver));
        }
        if (type.isReferenceType()) {
            ResolvedReferenceType result = type.asReferenceType();
            result = result.transformTypeParameters(typeParam -> replaceTypeParam(typeParam, tp, typeSolver))
                    .asReferenceType();
            return result;
        }
        throw new UnsupportedOperationException("Replacing " + type + ", param " + tp + " with "
                + type.getClass().getCanonicalName());
    }

    /**
     * Checks if a method usage is applicable for a given method name and parameter
     * types. This method performs type compatibility checking including generic
     * type variable substitution.
     * <p>
     * Limitation: the check is made on the declaration of the usage, not on the parameter types of the usage.
     * The substitution mentioned above is the one {@code isApplicable} applies to the declared types when an
     * argument does not match them directly, which replaces type variables by their bounds; the type arguments
     * already substituted into the usage are not taken into account. {@link #findMostApplicableUsage} therefore cannot tell apart overloads that only differ
     * by type variables of their declaring type, such as {@code set(T)} and {@code set(U)}, even when the usages
     * show them as {@code set(String)} and {@code set(Integer)}. Overload resolution on JavaParser declarations
     * does not go through it (see {@link #findMostApplicable(List, String, List, TypeSolver, Function)}).
     *
     * Note the specific naming here -- parameters are part of the method
     * declaration, while arguments are the values passed when calling a method.
     * Note that "needle" refers to that value being used as a search/query term to
     * match against.
     *
     * @return true, if the given MethodUsage matches the given name/types (normally
     *         obtained from a ResolvedMethodDeclaration)
     *
     * @see MethodResolutionLogic#isApplicable(ResolvedMethodDeclaration, String, List, TypeSolver)
     * @see MethodResolutionLogic#isApplicable(ResolvedMethodDeclaration, String, List, TypeSolver, boolean)
     */
    public static boolean isApplicable(
            MethodUsage methodUsage,
            String needleName,
            List<ResolvedType> needleParameterTypes,
            TypeSolver typeSolver) {
        return isApplicable(methodUsage.getDeclaration(), needleName, needleParameterTypes, typeSolver, false);
    }

    /**
     * The parameter types of {@code method} as declared, type variables included. It is the view used whenever
     * the type the method is looked up in is not known, and the default of every overload that does not take
     * parameter types.
     */
    private static List<ResolvedType> declaredParameterTypes(ResolvedMethodLikeDeclaration method) {
        List<ResolvedType> parameterTypes = new ArrayList<>(method.getNumberOfParams());
        for (int i = 0; i < method.getNumberOfParams(); i++) {
            parameterTypes.add(method.getParam(i).getType());
        }
        return parameterTypes;
    }

    /**
     * Checks if a primitive type can be boxed to a reference type (or vice versa).
     * Also handles wildcards.
     */
    private static boolean isBoxingCompatibleWithTypeSolver(
            ResolvedType expectedType, ResolvedType actualType, TypeSolver typeSolver) {
        // Handle null types
        if (expectedType == null || actualType == null) {
            return false;
        }
        // Handle wildcard types (e.g., ? extends Number, ? super Integer)
        if (expectedType.isWildcard()) {
            ResolvedWildcard wildcard = expectedType.asWildcard();
            if (wildcard.isBounded()) {
                // Check compatibility with the wildcard bound
                return isBoxingCompatibleWithTypeSolver(wildcard.getBoundedType(), actualType, typeSolver);
            }
            // Unbounded wildcard (?) - can accept anything via boxing
            return actualType.isPrimitive();
        }
        // Boxing never applies to array components (JLS 5.3): int[] is not compatible with Integer[] nor long[].
        // Array compatibility is fully handled by ResolvedArrayType#isAssignableBy.
        if (expectedType.isArray() || actualType.isArray()) {
            return false;
        }
        // Boxing (reference type expected, primitive provided)
        if (expectedType.isReferenceType() && actualType.isPrimitive()) {
            ResolvedReferenceType expectedRef = expectedType.asReferenceType();
            ResolvedPrimitiveType primitive = actualType.asPrimitive();
            // Get boxed type for the primitive (e.g., Integer for int)
            String boxedTypeQName = primitive.getBoxTypeQName();
            try {
                // Resolve the boxed type using TypeSolver
                ResolvedReferenceTypeDeclaration boxedTypeDecl = typeSolver.solveType(boxedTypeQName);
                ResolvedReferenceType boxedType = new ReferenceTypeImpl(boxedTypeDecl);
                // Check if boxed type is assignable to expected type
                // Example: Integer is assignable to Number
                return expectedRef.isAssignableBy(boxedType);
            } catch (Exception e) {
                // If we can't resolve the type, try a fallback check
                return false;
            }
        }
        // Unboxing (primitive expected, reference type provided)
        if (expectedType.isPrimitive() && actualType.isReferenceType()) {
            ResolvedPrimitiveType expectedPrimitive = expectedType.asPrimitive();
            ResolvedReferenceType actualRef = actualType.asReferenceType();
            // Check if actual type is a direct box type for the expected primitive
            if (ResolvedPrimitiveType.isBoxType(actualRef)) {
                Optional<ResolvedType> unboxed = ResolvedPrimitiveType.byBoxTypeQName(actualRef.getQualifiedName());
                return unboxed.isPresent() && unboxed.get().equals(expectedPrimitive);
            }
            // For other reference types, try to see if they can be assigned to the boxed type
            String expectedBoxedTypeQName = expectedPrimitive.getBoxTypeQName();
            try {
                ResolvedReferenceTypeDeclaration expectedBoxedTypeDecl = typeSolver.solveType(expectedBoxedTypeQName);
                ResolvedReferenceType expectedBoxedType = new ReferenceTypeImpl(expectedBoxedTypeDecl);
                // Check if actual type is assignable to the expected boxed type
                if (expectedBoxedType.isAssignableBy(actualRef)) {
                    // Then we can unbox
                    return true;
                }
            } catch (Exception e) {
                return false;
            }
        }
        // Unboxing (primitive expected, reference type provided)
        if (expectedType.isPrimitive() && actualType.isPrimitive()) {
            ResolvedPrimitiveType expectedPrimitive = expectedType.asPrimitive();
            ResolvedPrimitiveType actualPrimitive = actualType.asPrimitive();
            return expectedPrimitive.isAssignableBy(actualPrimitive);
        }
        // Both are reference types but one might be a constrained/wildcard type
        // This can happen after type variable substitution
        if (expectedType.isReferenceType() && actualType.isReferenceType()) {
            // This is not a boxing case, but we might want to check assignability
            // Let the main isApplicable logic handle this
            return false;
        }
        // Constraint types (e.g., LambdaConstraintType)
        if (actualType.isConstraint()) {
            // Check compatibility with the constraint bound
            return isBoxingCompatibleWithTypeSolver(
                    expectedType, actualType.asConstraintType().getBound(), typeSolver);
        }
        return false;
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
    public static SymbolReference<ResolvedMethodDeclaration> findMostApplicable(
            List<ResolvedMethodDeclaration> methods,
            String name,
            List<ResolvedType> argumentsTypes,
            TypeSolver typeSolver) {
        return findMostApplicable(
                methods, name, argumentsTypes, typeSolver, MethodResolutionLogic::declaredParameterTypes);
    }

    /**
     * @param methods we expect the methods to be ordered such that inherited methods are later in the list
     * @param parameterTypes gives the parameter types of a candidate as seen from the type the method is looked
     *     up in. A method inherited from a parameterized ancestor, such as {@code set(T)} inherited through
     *     {@code extends Base<String>}, must be compared on {@code set(String)}: overloads that only differ by
     *     type variables of the declaring type are otherwise indistinguishable.
     */
    public static SymbolReference<ResolvedMethodDeclaration> findMostApplicable(
            List<ResolvedMethodDeclaration> methods,
            String name,
            List<ResolvedType> argumentsTypes,
            TypeSolver typeSolver,
            Function<ResolvedMethodDeclaration, List<ResolvedType>> parameterTypes) {
        // A first pass without wildcard tolerance, then a second one with it, as for the declared signatures
        SymbolReference<ResolvedMethodDeclaration> res =
                findMostApplicable(methods, name, argumentsTypes, typeSolver, false, parameterTypes);
        if (res.isSolved()) {
            return res;
        }
        return findMostApplicable(methods, name, argumentsTypes, typeSolver, true, parameterTypes);
    }

    public static SymbolReference<ResolvedMethodDeclaration> findMostApplicable(
            List<ResolvedMethodDeclaration> methods,
            String name,
            List<ResolvedType> argumentsTypes,
            TypeSolver typeSolver,
            boolean wildcardTolerance) {
        return findMostApplicable(
                methods,
                name,
                argumentsTypes,
                typeSolver,
                wildcardTolerance,
                MethodResolutionLogic::declaredParameterTypes);
    }

    /**
     * Keeps the candidates applicable to {@code argumentsTypes} and selects the most specific one. Both steps
     * compare the candidates on the same {@code parameterTypes}: a candidate found applicable on its parameter
     * types as seen from the receiver must also be ranked on them, otherwise {@code set(String)} and
     * {@code set(Integer)} would be ranked as the indistinguishable {@code set(T)} and {@code set(U)}.
     */
    private static SymbolReference<ResolvedMethodDeclaration> findMostApplicable(
            List<ResolvedMethodDeclaration> methods,
            String name,
            List<ResolvedType> argumentsTypes,
            TypeSolver typeSolver,
            boolean wildcardTolerance,
            Function<ResolvedMethodDeclaration, List<ResolvedType>> parameterTypes) {
        List<ResolvedMethodDeclaration> applicableMethods = methods.stream()
                .filter(m -> m.getName().equals(name))
                .filter(distinctByKey(ResolvedMethodDeclaration::getQualifiedSignature))
                .filter(m ->
                        isApplicable(m, parameterTypes.apply(m), name, argumentsTypes, typeSolver, wildcardTolerance))
                .collect(Collectors.toList());
        Optional<ResolvedMethodDeclaration> result = selectMostApplicable(
                applicableMethods,
                argumentsTypes,
                Function.identity(),
                parameterTypes,
                ResolvedMethodDeclaration::declaringType);
        return result.map(SymbolReference::solved).orElseGet(SymbolReference::unsolved);
    }

    protected static boolean isExactMatch(ResolvedMethodLikeDeclaration method, List<ResolvedType> argumentsTypes) {
        return isExactMatch(method, declaredParameterTypes(method), argumentsTypes);
    }

    /**
     * Whether every argument has exactly the type of the matching parameter, the parameter types being
     * {@code parameterTypes} rather than the declared ones. It settles a possible ambiguity between candidates
     * that are equally specific.
     */
    private static boolean isExactMatch(
            ResolvedMethodLikeDeclaration method,
            List<ResolvedType> parameterTypes,
            List<ResolvedType> argumentsTypes) {
        for (int i = 0; i < method.getNumberOfParams(); i++) {
            ResolvedType paramType = explicitAndVariadicParameterType(method, parameterTypes, i);
            if (paramType == null) {
                return false;
            }
            if (i >= argumentsTypes.size()) {
                return false;
            }
            if (!paramType.equals(argumentsTypes.get(i))) {
                return false;
            }
        }
        return true;
    }

    public static ResolvedType getMethodsExplicitAndVariadicParameterType(ResolvedMethodLikeDeclaration method, int i) {
        int numberOfParams = method.getNumberOfParams();
        if (i < numberOfParams) {
            return method.getParam(i).getType();
        }
        if (method.hasVariadicParameter()) {
            return method.getParam(numberOfParams - 1).getType();
        }
        return null;
    }

    public static ResolvedType getMethodUsageExplicitAndVariadicParameterType(MethodUsage method, int i) {
        int numberOfParams = method.getNoParams();
        if (i < numberOfParams) {
            return method.getParamType(i);
        }
        if (method.getDeclaration().hasVariadicParameter()) {
            return method.getParamType(numberOfParams - 1);
        }
        return null;
    }

    /**
     * Same as {@link #getMethodsExplicitAndVariadicParameterType(ResolvedMethodLikeDeclaration, int)}, the type
     * being taken from {@code parameterTypes}: the type of the {@code i}-th parameter, or of the variadic
     * parameter when the {@code i}-th argument is one of the values it groups, or {@code null} when the method
     * has no parameter for that argument.
     */
    private static ResolvedType explicitAndVariadicParameterType(
            ResolvedMethodLikeDeclaration method, List<ResolvedType> parameterTypes, int i) {
        int numberOfParams = parameterTypes.size();
        if (i < numberOfParams) {
            return parameterTypes.get(i);
        }
        if (method.hasVariadicParameter()) {
            return parameterTypes.get(numberOfParams - 1);
        }
        return null;
    }

    static boolean isMoreSpecific(
            ResolvedMethodLikeDeclaration methodA,
            ResolvedMethodLikeDeclaration methodB,
            List<ResolvedType> argumentTypes) {
        return isMoreSpecific(
                methodA, declaredParameterTypes(methodA), methodB, declaredParameterTypes(methodB), argumentTypes);
    }

    /**
     * Whether {@code methodA} is more specific than {@code methodB} for {@code argumentTypes} (JLS 15.12.2.5),
     * each method being compared on its own parameter types, {@code parameterTypesA} and
     * {@code parameterTypesB}. Variadic parameters are still identified on the declarations.
     */
    private static boolean isMoreSpecific(
            ResolvedMethodLikeDeclaration methodA,
            List<ResolvedType> parameterTypesA,
            ResolvedMethodLikeDeclaration methodB,
            List<ResolvedType> parameterTypesB,
            List<ResolvedType> argumentTypes) {
        final boolean aVariadic = methodA.hasVariadicParameter();
        final boolean bVariadic = methodB.hasVariadicParameter();
        final int aNumberOfParams = methodA.getNumberOfParams();
        final int bNumberOfParams = methodB.getNumberOfParams();
        final int numberOfArgs = argumentTypes.size();
        final ResolvedType lastArgType = numberOfArgs > 0 ? argumentTypes.get(numberOfArgs - 1) : null;
        final boolean isLastArgArray = lastArgType != null && lastArgType.isArray();
        int omittedArgs = 0;
        boolean isMethodAMoreSpecific = false;
        // If one method declaration has exactly the correct amount of parameters and is not variadic then it is always
        // preferred to a declaration that is variadic (and hence possibly also has a different amount of parameters).
        if (!aVariadic
                && aNumberOfParams == numberOfArgs
                && (bVariadic && (bNumberOfParams != numberOfArgs || !isLastArgArray))) {
            return true;
        }
        if (!bVariadic
                && bNumberOfParams == numberOfArgs
                && (aVariadic && (aNumberOfParams != numberOfArgs || !isLastArgArray))) {
            return false;
        }
        // If both methods are variadic but the calling method omits any varArgs, bump the omitted args to
        // ensure the varargs type is considered when determining which method is more specific
        if (aVariadic && bVariadic && aNumberOfParams == bNumberOfParams && numberOfArgs == aNumberOfParams - 1) {
            omittedArgs++;
        }
        // Either both methods are variadic or neither is. So we must compare the parameter types.
        for (int i = 0; i < numberOfArgs + omittedArgs; i++) {
            ResolvedType paramTypeA = explicitAndVariadicParameterType(methodA, parameterTypesA, i);
            ResolvedType paramTypeB = explicitAndVariadicParameterType(methodB, parameterTypesB, i);
            ResolvedType argType = null;
            if (i < argumentTypes.size()) {
                argType = argumentTypes.get(i);
            }
            // Safety: if a type is null it means a signature with too few parameters managed to get to this point.
            // This should not happen but it also means that this signature is immediately disqualified.
            if (paramTypeA == null) {
                return false;
            }
            if (paramTypeB == null) {
                return true;
            }
            // Widening primitive conversions have priority over boxing/unboxing conversions when finding the most
            // applicable method. E.g. assume we have method call foo(1) and declarations foo(long) and foo(Integer).
            // The method call will call foo(long), as it requires a widening primitive conversion from int to long
            // instead of a boxing conversion from int to Integer. See JLS §15.12.2.
            // This is what we check here.
            if (argType != null
                    && paramTypeA.isPrimitive() == argType.isPrimitive()
                    && paramTypeB.isPrimitive() != argType.isPrimitive()
                    && paramTypeA.isAssignableBy(argType)) {
                return true;
            }
            if (argType != null
                    && paramTypeB.isPrimitive() == argType.isPrimitive()
                    && paramTypeA.isPrimitive() != argType.isPrimitive()
                    && paramTypeB.isAssignableBy(argType)) {
                return false;
                // if paramA and paramB are not the last parameters
                // and the type of paramA or paramB (which are not more specific at this stage) is java.lang.Object
                // then we have to consider others parameters before concluding
            }
            if ((i < numberOfArgs - 1) && (isJavaLangObject(paramTypeB) || (isJavaLangObject(paramTypeA)))) {
                // consider others parameters
                // but eventually mark the method A as more specific if the methodB has an argument of type
                // java.lang.Object
                isMethodAMoreSpecific = isMethodAMoreSpecific || isJavaLangObject(paramTypeB);
            } else {
                // If we get to this point then we check whether one of the methods contains a parameter type that is
                // more specific. If it does, we can assume the entire declaration is more specific as we would
                // otherwise have a situation where the declarations are ambiguous in the given context.
                // Note: This does not account for the case where one parameter is variadic (and therefore an array
                // type) and the other is not, since these will never be assignable by each other. This case is checked
                // below.
                boolean aAssignableFromB = paramTypeA.isAssignableBy(paramTypeB);
                boolean bAssignableFromA = paramTypeB.isAssignableBy(paramTypeA);
                if (bAssignableFromA && !aAssignableFromB) {
                    // A's parameter is more specific
                    return true;
                }
                if (aAssignableFromB && !bAssignableFromA) {
                    // B's parameter is more specific
                    return false;
                }
            }
            // Note on safety: methodX.getParam(i) is safe because otherwise paramTypeX would be null, but add
            // a check in case this changes in the future.
            if (methodA.getNumberOfParams() > i && methodB.getNumberOfParams() > i) {
                boolean paramAVariadic = methodA.getParam(i).isVariadic();
                boolean paramBVariadic = methodB.getParam(i).isVariadic();
                // Prefer a single parameter over a variadic parameter, e.g.
                // foo(String s, Object... o) is preferred over foo(Object... o)
                if (!paramAVariadic && paramBVariadic) {
                    return true;
                }
            }
        }
        if (aVariadic && !bVariadic) {
            // if the last argument is an array then m1 is more specific
            return isLastArgArray;
        }
        if (!aVariadic && bVariadic) {
            // if the last argument is an array and m1 is not variadic then
            // it is not more specific
            return !isLastArgArray;
        }
        return isMethodAMoreSpecific;
    }

    private static boolean isJavaLangObject(ResolvedType paramType) {
        return paramType.isReferenceType()
                && paramType.asReferenceType().getQualifiedName().equals("java.lang.Object");
    }

    /**
     * Same as {@link #isMoreSpecific(ResolvedMethodLikeDeclaration, List, ResolvedMethodLikeDeclaration, List, List)}
     * for the candidates handled by {@link #selectMostApplicable}, whatever their representation.
     */
    private static <T> boolean isMoreSpecific(
            T candidateA,
            T candidateB,
            List<ResolvedType> argumentTypes,
            Function<T, ResolvedMethodDeclaration> toDeclaration,
            Function<T, List<ResolvedType>> toParameterTypes) {
        return isMoreSpecific(
                toDeclaration.apply(candidateA),
                toParameterTypes.apply(candidateA),
                toDeclaration.apply(candidateB),
                toParameterTypes.apply(candidateB),
                argumentTypes);
    }

    public static Optional<MethodUsage> findMostApplicableUsage(
            List<MethodUsage> methods, String name, List<ResolvedType> argumentsTypes, TypeSolver typeSolver) {
        List<MethodUsage> applicableMethods = methods.stream()
                .filter((m) -> isApplicable(m, name, argumentsTypes, typeSolver))
                .collect(Collectors.toList());
        // The usages are ranked on their declared signatures, as isApplicable(MethodUsage, ...) checks them
        return selectMostApplicable(
                applicableMethods,
                argumentsTypes,
                MethodUsage::getDeclaration,
                m -> declaredParameterTypes(m.getDeclaration()),
                MethodUsage::declaringType);
    }

    private static boolean areOverride(ResolvedMethodDeclaration a, ResolvedMethodDeclaration b) {
        if (!a.getName().equals(b.getName())) {
            return false;
        }
        if (a.getNumberOfParams() != b.getNumberOfParams()) {
            return false;
        }
        for (int i = 0; i < a.getNumberOfParams(); i++) {
            if (!a.getParam(i).getType().equals(b.getParam(i).getType())) {
                return false;
            }
        }
        return true;
    }

    /**
     * Selects the most applicable candidate from a list of already-filtered applicable methods.
     * This is the shared selection logic used by both {@link #findMostApplicable} and
     * {@link #findMostApplicableUsage}.
     *
     * @param <T>               the candidate type (ResolvedMethodDeclaration or MethodUsage)
     * @param applicableMethods the list of candidates that have already passed applicability checks
     * @param argumentsTypes    the argument types at the call site
     * @param toDeclaration     extracts the ResolvedMethodDeclaration from a candidate
     * @param toParameterTypes  extracts the parameter types a candidate is compared on
     * @param toDeclaringType   extracts the declaring type from a candidate
     * @return the most applicable candidate, or empty if the list is empty
     */
    private static <T> Optional<T> selectMostApplicable(
            List<T> applicableMethods,
            List<ResolvedType> argumentsTypes,
            Function<T, ResolvedMethodDeclaration> toDeclaration,
            Function<T, List<ResolvedType>> toParameterTypes,
            Function<T, ResolvedReferenceTypeDeclaration> toDeclaringType) {
        if (applicableMethods.isEmpty()) {
            return Optional.empty();
        }
        if (applicableMethods.size() == 1) {
            return Optional.of(applicableMethods.get(0));
        }
        // Filter out candidates with array parameters when null arguments are present,
        // since non-array overloads are preferred for null values.
        applicableMethods = filterByNullArgs(applicableMethods, argumentsTypes, toDeclaration);
        if (applicableMethods.size() == 1) {
            return Optional.of(applicableMethods.get(0));
        }
        T winningCandidate = applicableMethods.get(0);
        T other = null;
        boolean possibleAmbiguity = false;
        for (int i = 1; i < applicableMethods.size(); i++) {
            other = applicableMethods.get(i);
            if (isMoreSpecific(winningCandidate, other, argumentsTypes, toDeclaration, toParameterTypes)) {
                possibleAmbiguity = false;
            } else if (isMoreSpecific(other, winningCandidate, argumentsTypes, toDeclaration, toParameterTypes)) {
                possibleAmbiguity = false;
                winningCandidate = other;
            } else {
                ResolvedMethodDeclaration winningDecl = toDeclaration.apply(winningCandidate);
                ResolvedMethodDeclaration otherDecl = toDeclaration.apply(other);
                if (winningDecl.isGeneric() && !otherDecl.isGeneric()) {
                    winningCandidate = other;
                } else if (!winningDecl.isGeneric() && otherDecl.isGeneric()) {
                    // winningCandidate stays
                } else if (toDeclaringType
                        .apply(winningCandidate)
                        .getQualifiedName()
                        .equals(toDeclaringType.apply(other).getQualifiedName())) {
                    possibleAmbiguity = true;
                } else {
                    // we expect the methods to be ordered such that inherited methods are later in the list
                }
            }
        }
        if (possibleAmbiguity) {
            ResolvedMethodDeclaration winningDecl = toDeclaration.apply(winningCandidate);
            ResolvedMethodDeclaration otherDecl = toDeclaration.apply(other);
            if (areOverride(winningDecl, otherDecl)) {
                // Same method inherited via multiple paths — not a real ambiguity
            } else if (!isExactMatch(winningDecl, toParameterTypes.apply(winningCandidate), argumentsTypes)) {
                if (isExactMatch(otherDecl, toParameterTypes.apply(other), argumentsTypes)) {
                    winningCandidate = other;
                } else {
                    throw new MethodAmbiguityException("Ambiguous method call: cannot find a most applicable method: "
                            + winningCandidate + ", " + other + ". First declared in "
                            + toDeclaringType.apply(winningCandidate).getQualifiedName());
                }
            }
        }
        return Optional.of(winningCandidate);
    }

    /**
     * When null arguments are present, filter out candidates that have array parameters
     * at those positions, since non-array overloads are preferred for null values.
     */
    private static <T> List<T> filterByNullArgs(
            List<T> applicableMethods,
            List<ResolvedType> argumentsTypes,
            Function<T, ResolvedMethodDeclaration> toDeclaration) {
        List<Integer> nullParamIndexes = new ArrayList<>();
        for (int i = 0; i < argumentsTypes.size(); i++) {
            if (argumentsTypes.get(i).isNull()) {
                nullParamIndexes.add(i);
            }
        }
        if (nullParamIndexes.isEmpty()) {
            return applicableMethods;
        }
        Set<T> removeCandidates = new HashSet<>();
        for (Integer nullParamIndex : nullParamIndexes) {
            for (T candidate : applicableMethods) {
                if (toDeclaration
                        .apply(candidate)
                        .getParam(nullParamIndex)
                        .getType()
                        .isArray()) {
                    removeCandidates.add(candidate);
                }
            }
        }
        if (!removeCandidates.isEmpty() && removeCandidates.size() < applicableMethods.size()) {
            List<T> filtered = new ArrayList<>(applicableMethods);
            filtered.removeAll(removeCandidates);
            return filtered;
        }
        return applicableMethods;
    }

    public static SymbolReference<ResolvedMethodDeclaration> solveMethodInType(
            ResolvedTypeDeclaration typeDeclaration, String name, List<ResolvedType> argumentsTypes) {
        return solveMethodInType(typeDeclaration, name, argumentsTypes, false);
    }

    // TODO: Replace TypeDeclaration.solveMethod
    public static SymbolReference<ResolvedMethodDeclaration> solveMethodInType(
            ResolvedTypeDeclaration typeDeclaration,
            String name,
            List<ResolvedType> argumentsTypes,
            boolean staticOnly) {
        if (typeDeclaration instanceof MethodResolutionCapability) {
            return ((MethodResolutionCapability) typeDeclaration).solveMethod(name, argumentsTypes, staticOnly);
        }
        throw new UnsupportedOperationException(typeDeclaration.getClass().getCanonicalName());
    }

    /**
     * Same as {@link #solveMethodInType(ResolvedTypeDeclaration, String, List, boolean)}, for a call on a
     * receiver of type {@code receiverType}, whose type arguments distinguish overloads that only differ by
     * type variables of the declaring type.
     */
    public static SymbolReference<ResolvedMethodDeclaration> solveMethodInType(
            ResolvedReferenceType receiverType, String name, List<ResolvedType> argumentsTypes, boolean staticOnly) {
        ResolvedReferenceTypeDeclaration typeDeclaration = receiverType
                .getTypeDeclaration()
                .orElseThrow(() -> new UnsupportedOperationException(receiverType.describe()));
        if (typeDeclaration instanceof MethodResolutionCapability) {
            // The declaration decides what to do with the type arguments: by default they are ignored and the
            // call is resolved as by solveMethodInType(typeDeclaration, ...)
            return ((MethodResolutionCapability) typeDeclaration)
                    .solveMethod(name, argumentsTypes, staticOnly, receiverType.typeParametersValues());
        }
        throw new UnsupportedOperationException(typeDeclaration.getClass().getCanonicalName());
    }

    public static void inferTypes(
            ResolvedType source, ResolvedType target, Map<ResolvedTypeParameterDeclaration, ResolvedType> mappings) {
        if (source.equals(target)) {
            return;
        }
        if (source.isReferenceType() && target.isReferenceType()) {
            ResolvedReferenceType sourceRefType = source.asReferenceType();
            ResolvedReferenceType targetRefType = target.asReferenceType();
            if (sourceRefType.getQualifiedName().equals(targetRefType.getQualifiedName())) {
                if (!sourceRefType.isRawType() && !targetRefType.isRawType()) {
                    for (int i = 0; i < sourceRefType.typeParametersValues().size(); i++) {
                        inferTypes(
                                sourceRefType.typeParametersValues().get(i),
                                targetRefType.typeParametersValues().get(i),
                                mappings);
                    }
                }
            } else {
                // source may be a subtype of target — walk source's ancestors to find a match
                for (ResolvedReferenceType ancestor : sourceRefType.getAllAncestors()) {
                    if (ancestor.getQualifiedName().equals(targetRefType.getQualifiedName())) {
                        inferTypes(ancestor, target, mappings);
                        break;
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
            if (source.asWildcard().isBounded() && target.asWildcard().isBounded()) {
                inferTypes(
                        source.asWildcard().getBoundedType(),
                        target.asWildcard().getBoundedType(),
                        mappings);
            }
            return;
        }
        if (source.isReferenceType() && target.isTypeVariable()) {
            mappings.put(target.asTypeParameter(), source);
            return;
        }
        if (source.isWildcard() && target.isTypeVariable()) {
            mappings.put(target.asTypeParameter(), source);
            return;
        }
        if (source.isArray() && target.isArray()) {
            ResolvedType sourceComponentType = source.asArrayType().getComponentType();
            ResolvedType targetComponentType = target.asArrayType().getComponentType();
            inferTypes(sourceComponentType, targetComponentType, mappings);
            return;
        }
        if (source.isArray() && target.isWildcard()) {
            if (target.asWildcard().isBounded()) {
                inferTypes(source, target.asWildcard().getBoundedType(), mappings);
                return;
            }
            return;
        }
        if (source.isArray() && target.isTypeVariable()) {
            mappings.put(target.asTypeParameter(), source);
            return;
        }
        if (source.isWildcard() && target.isReferenceType()) {
            if (source.asWildcard().isBounded()) {
                inferTypes(source.asWildcard().getBoundedType(), target, mappings);
            }
            return;
        }
        if (source.isConstraint() && target.isReferenceType()) {
            inferTypes(source.asConstraintType().getBound(), target, mappings);
            return;
        }
        if (source.isConstraint() && target.isTypeVariable()) {
            inferTypes(source.asConstraintType().getBound(), target, mappings);
            return;
        }
        if (source.isTypeVariable() && target.isTypeVariable()) {
            mappings.put(target.asTypeParameter(), source);
            return;
        }
        if (source.isTypeVariable()) {
            inferTypes(target, source, mappings);
            return;
        }
        if (source.isPrimitive() || target.isPrimitive()) {
            return;
        }
        if (source.isNull()) {
            return;
        }
        if (target.isReferenceType()) {
            ResolvedReferenceType formalTypeAsReference = target.asReferenceType();
            if (formalTypeAsReference.isJavaLangObject()) {
                return;
            }
        }
    }
}
