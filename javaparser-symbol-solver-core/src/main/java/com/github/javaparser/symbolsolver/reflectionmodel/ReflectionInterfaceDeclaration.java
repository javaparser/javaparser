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

package com.github.javaparser.symbolsolver.reflectionmodel;

import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.resolution.Context;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.logic.ConflictingGenericTypesException;
import com.github.javaparser.resolution.logic.InferenceContext;
import com.github.javaparser.resolution.logic.MethodResolutionCapability;
import com.github.javaparser.resolution.model.LambdaArgumentTypePlaceholder;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.model.typesystem.NullType;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.core.resolution.MethodUsageResolutionCapability;
import com.github.javaparser.symbolsolver.core.resolution.SymbolResolutionCapability;
import com.github.javaparser.symbolsolver.logic.AbstractTypeDeclaration;
import java.lang.reflect.Field;
import java.util.*;
import java.util.stream.Collectors;

/**
 * @author Federico Tomassetti
 */
public class ReflectionInterfaceDeclaration extends AbstractTypeDeclaration
        implements ResolvedInterfaceDeclaration,
                MethodResolutionCapability,
                MethodUsageResolutionCapability,
                SymbolResolutionCapability {

    ///
    /// Fields
    ///

    private Class<?> clazz;
    private TypeSolver typeSolver;
    private ReflectionClassAdapter reflectionClassAdapter;

    ///
    /// Constructor
    ///

    public ReflectionInterfaceDeclaration(Class<?> clazz, TypeSolver typeSolver) {
        if (!clazz.isInterface()) {
            throw new IllegalArgumentException();
        }

        this.clazz = clazz;
        this.typeSolver = typeSolver;
        this.reflectionClassAdapter = new ReflectionClassAdapter(clazz, typeSolver, this);
    }

    ///
    /// Public methods
    ///

    @Override
    public boolean isAssignableBy(ResolvedReferenceTypeDeclaration other) {
        return isAssignableBy(new ReferenceTypeImpl(other));
    }

    @Override
    public String getPackageName() {
        if (clazz.getPackage() != null) {
            return clazz.getPackage().getName();
        }
        return null;
    }

    @Override
    public String getClassName() {
        String canonicalName = clazz.getCanonicalName();
        if (canonicalName != null && getPackageName() != null) {
            return canonicalName.substring(getPackageName().length() + 1);
        }
        return null;
    }

    @Override
    public String getQualifiedName() {
        return clazz.getCanonicalName();
    }

    @Override
    @Deprecated
    public SymbolReference<ResolvedMethodDeclaration> solveMethod(
            String name, List<ResolvedType> parameterTypes, boolean staticOnly) {
        return ReflectionMethodResolutionLogic.solveMethod(name, parameterTypes, staticOnly, typeSolver, this, clazz);
    }

    @Override
    public String toString() {
        return "ReflectionInterfaceDeclaration{" + "clazz=" + clazz.getCanonicalName() + '}';
    }

    public ResolvedType getUsage(Node node) {
        return new ReferenceTypeImpl(this);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof ReflectionInterfaceDeclaration)) return false;

        ReflectionInterfaceDeclaration that = (ReflectionInterfaceDeclaration) o;

        if (!clazz.getCanonicalName().equals(that.clazz.getCanonicalName())) return false;

        return getTypeParameters().equals(that.getTypeParameters());
    }

    @Override
    public int hashCode() {
        return clazz.hashCode();
    }

    /**
     * Solves method usage with proper generic type inference, including support for varargs methods.
     * This method first resolves the basic method signature, then performs generic type inference
     * based on the actual parameter types provided at the call site.
     *
     * @param name the method name to resolve
     * @param parameterTypes the actual parameter types at the call site
     * @param invokationContext the context where the method is invoked
     * @param typeParameterValues explicit type parameter values (if any)
     * @return an Optional containing the resolved MethodUsage with inferred types, or empty if resolution fails
     */
    public Optional<MethodUsage> solveMethodAsUsage(
            String name,
            List<ResolvedType> parameterTypes,
            Context invokationContext,
            List<ResolvedType> typeParameterValues) {

        Optional<MethodUsage> res = ReflectionMethodResolutionLogic.solveMethodAsUsage(
                name, parameterTypes, typeSolver, invokationContext, typeParameterValues, this, clazz);

        if (!res.isPresent()) {
            return res;
        }

        return performTypeInference(res.get(), parameterTypes);
    }

    /**
     * Performs generic type inference on a resolved method usage by analyzing the relationship
     * between formal parameter types and actual parameter types provided at the call site.
     * Handles both regular methods and varargs methods with appropriate constraint collection.
     *
     * @param methodUsage the initially resolved method usage
     * @param parameterTypes the actual parameter types from the call site
     * @return an Optional containing the method usage with inferred generic types, or empty if inference fails
     */
    private Optional<MethodUsage> performTypeInference(MethodUsage methodUsage, List<ResolvedType> parameterTypes) {
        try {
            InferenceContext inferenceContext = new InferenceContext(typeSolver);
            List<ResolvedType> constraintPairs = collectTypeConstraints(methodUsage, parameterTypes, inferenceContext);
            return resolveInferredTypes(methodUsage, constraintPairs, inferenceContext);
        } catch (ConflictingGenericTypesException e) {
            return Optional.empty();
        }
    }

    /**
     * Collects type constraints by comparing formal parameter types with actual parameter types.
     * Automatically detects whether the method is varargs and delegates to the appropriate
     * constraint collection strategy. Also validates that parameter counts are compatible.
     *
     * @param methodUsage the method usage to analyze
     * @param parameterTypes the actual parameter types from the call site
     * @param inferenceContext the inference context for collecting type constraints
     * @return a list of type constraints that will be used for generic type resolution
     * @throws IllegalArgumentException if parameter counts are incompatible
     */
    private List<ResolvedType> collectTypeConstraints(
            MethodUsage methodUsage, List<ResolvedType> parameterTypes, InferenceContext inferenceContext) {

        boolean isVarArgs = methodUsage.getDeclaration().hasVariadicParameter();
        int formalParamCount = methodUsage.getNoParams();
        int actualParamCount = parameterTypes.size();

        validateParameterCount(isVarArgs, formalParamCount, actualParamCount);

        if (isVarArgs) {
            return collectVarArgsConstraints(methodUsage, parameterTypes, inferenceContext, formalParamCount);
        } else {
            return collectRegularConstraints(methodUsage, parameterTypes, inferenceContext);
        }
    }

    /**
     * Validates that the number of actual parameters is compatible with the method signature.
     * For regular methods, counts must match exactly. For varargs methods, actual parameter
     * count must be at least the number of required parameters (formal count - 1).
     *
     * @param isVarArgs whether the method is a varargs method
     * @param formalParamCount the number of formal parameters in the method signature
     * @param actualParamCount the number of actual parameters provided at the call site
     * @throws IllegalArgumentException if parameter counts are incompatible
     */
    private void validateParameterCount(boolean isVarArgs, int formalParamCount, int actualParamCount) {
        if (isVarArgs && actualParamCount < formalParamCount - 1) {
            throw new IllegalArgumentException("Too few parameters for varargs method");
        }
        if (!isVarArgs && actualParamCount != formalParamCount) {
            throw new IllegalArgumentException("Parameter count mismatch for non-varargs method");
        }
    }

    /**
     * Collects type constraints for regular (non-varargs) methods by creating pairs
     * between each formal parameter type and its corresponding actual parameter type.
     * This is a straightforward one-to-one mapping since parameter counts must match exactly.
     *
     * @param methodUsage the method usage to analyze
     * @param parameterTypes the actual parameter types from the call site
     * @param inferenceContext the inference context for collecting constraints
     * @return a list of type constraints, one for each parameter position
     */
    private List<ResolvedType> collectRegularConstraints(
            MethodUsage methodUsage, List<ResolvedType> parameterTypes, InferenceContext inferenceContext) {
        List<ResolvedType> constraints = new LinkedList<>();

        for (int i = 0; i < parameterTypes.size(); i++) {
            ResolvedType formalType = methodUsage.getParamType(i);
            ResolvedType actualType = parameterTypes.get(i);
            constraints.add(inferenceContext.addPair(formalType, actualType));
        }

        return constraints;
    }

    /**
     * Collects type constraints for varargs methods. This involves two phases:
     * 1. Regular parameters: handled like non-varargs methods (one-to-one mapping)
     * 2. Varargs parameter: handled specially based on how arguments are passed
     *
     * The varargs parameter can receive arguments in two ways:
     * - Direct array passing: method(array) - constraint between array types
     * - Individual elements: method(elem1, elem2, ...) - constraints between component type and each element
     *
     * @param methodUsage the varargs method usage to analyze
     * @param parameterTypes the actual parameter types from the call site
     * @param inferenceContext the inference context for collecting constraints
     * @param formalParamCount the total number of formal parameters (including varargs)
     * @return a list of type constraints covering both regular and varargs parameters
     */
    private List<ResolvedType> collectVarArgsConstraints(
            MethodUsage methodUsage,
            List<ResolvedType> parameterTypes,
            InferenceContext inferenceContext,
            int formalParamCount) {
        List<ResolvedType> constraints = new LinkedList<>();
        int regularParamCount = formalParamCount - 1;

        // Process regular parameters
        for (int i = 0; i < regularParamCount; i++) {
            ResolvedType formalType = methodUsage.getParamType(i);
            ResolvedType actualType = parameterTypes.get(i);
            constraints.add(inferenceContext.addPair(formalType, actualType));
        }

        // Process varargs parameter
        if (formalParamCount > 0) {
            ResolvedType varargsParamType = methodUsage.getParamType(regularParamCount);
            processVarArgsParameter(varargsParamType, parameterTypes, regularParamCount, inferenceContext, constraints);
        }

        return constraints;
    }

    /**
     * Processes the varargs parameter by determining how arguments are passed and creating
     * appropriate type constraints. Handles two scenarios:
     *
     * 1. Direct array passing: When exactly one argument is passed to varargs and it's an array,
     *    creates a constraint between the formal array type and the actual array type.
     *    Example: method(String[] args) called as method(stringArray)
     *
     * 2. Individual element passing: When multiple arguments are passed to varargs,
     *    creates constraints between the array's component type and each individual argument.
     *    Example: method(String... args) called as method("a", "b", "c")
     *
     * @param varargsParamType the formal type of the varargs parameter (must be an array type)
     * @param parameterTypes all actual parameter types from the call site
     * @param regularParamCount the number of regular (non-varargs) parameters
     * @param inferenceContext the inference context for collecting constraints
     * @param constraints the constraint list to add new constraints to
     * @throws IllegalStateException if the varargs parameter is not an array type
     */
    private void processVarArgsParameter(
            ResolvedType varargsParamType,
            List<ResolvedType> parameterTypes,
            int regularParamCount,
            InferenceContext inferenceContext,
            List<ResolvedType> constraints) {
        if (!varargsParamType.isArray()) {
            throw new IllegalStateException("Varargs parameter is not an array type");
        }

        ResolvedType componentType = varargsParamType.asArrayType().getComponentType();
        int actualParamCount = parameterTypes.size();

        if (isDirectArrayPassing(parameterTypes, regularParamCount, actualParamCount)) {
            // Direct array passing: method(array)
            ResolvedType actualArrayType = parameterTypes.get(regularParamCount);
            constraints.add(inferenceContext.addPair(varargsParamType, actualArrayType));
        } else {
            // Individual elements passing: method(elem1, elem2, ...)
            for (int i = regularParamCount; i < actualParamCount; i++) {
                ResolvedType actualType = parameterTypes.get(i);
                constraints.add(inferenceContext.addPair(componentType, actualType));
            }
        }
    }

    /**
     * Determines whether arguments are being passed directly as an array to the varargs parameter.
     * This happens when there is exactly one argument for the varargs parameter and that argument
     * is an array type. This is a special case that requires different constraint handling.
     *
     * @param parameterTypes all actual parameter types from the call site
     * @param regularParamCount the number of regular (non-varargs) parameters
     * @param actualParamCount the total number of actual parameters
     * @return true if a single array is being passed directly to varargs, false otherwise
     */
    private boolean isDirectArrayPassing(
            List<ResolvedType> parameterTypes, int regularParamCount, int actualParamCount) {
        return actualParamCount == regularParamCount + 1
                && parameterTypes.get(regularParamCount).isArray();
    }

    /**
     * Applies the inferred generic types to the method usage by resolving all collected constraints
     * and updating both parameter types and return type with their concrete resolved types.
     * This is the final step that produces a fully resolved MethodUsage with no remaining generic placeholders.
     *
     * @param methodUsage the method usage to update with resolved types
     * @param constraints the collected type constraints from parameter analysis
     * @param inferenceContext the inference context containing all type relationships
     * @return an Optional containing the fully resolved MethodUsage
     * @throws ConflictingGenericTypesException if type constraints are contradictory
     */
    private Optional<MethodUsage> resolveInferredTypes(
            MethodUsage methodUsage, List<ResolvedType> constraints, InferenceContext inferenceContext) {
        // Resolve return type
        ResolvedType returnType = inferenceContext.addSingle(methodUsage.returnType());

        // Apply resolved parameter types
        for (int i = 0; i < constraints.size() && i < methodUsage.getNoParams(); i++) {
            ResolvedType resolvedParamType = inferenceContext.resolve(constraints.get(i));
            methodUsage = methodUsage.replaceParamType(i, resolvedParamType);
        }

        // Apply resolved return type
        methodUsage = methodUsage.replaceReturnType(inferenceContext.resolve(returnType));

        return Optional.of(methodUsage);
    }

    @Override
    public boolean canBeAssignedTo(ResolvedReferenceTypeDeclaration other) {
        if (other instanceof LambdaArgumentTypePlaceholder) {
            return isFunctionalInterface();
        }
        if (other.getQualifiedName().equals(getQualifiedName())) {
            return true;
        }
        if (this.clazz.getSuperclass() != null
                && new ReflectionInterfaceDeclaration(clazz.getSuperclass(), typeSolver).canBeAssignedTo(other)) {
            return true;
        }
        for (Class interfaze : clazz.getInterfaces()) {
            if (new ReflectionInterfaceDeclaration(interfaze, typeSolver).canBeAssignedTo(other)) {
                return true;
            }
        }

        // Everything can be assigned to {@code java.lang.Object}
        return other.isJavaLangObject();
    }

    @Override
    public boolean isAssignableBy(ResolvedType type) {
        if (type instanceof NullType) {
            return true;
        }
        if (type instanceof LambdaArgumentTypePlaceholder) {
            return isFunctionalInterface();
        }
        if (type.isArray()) {
            return false;
        }
        if (type.isPrimitive()) {
            return false;
        }
        if (type.describe().equals(getQualifiedName())) {
            return true;
        }
        if (type instanceof ReferenceTypeImpl) {
            ReferenceTypeImpl otherTypeDeclaration = (ReferenceTypeImpl) type;
            if (otherTypeDeclaration.getTypeDeclaration().isPresent()) {
                return otherTypeDeclaration.getTypeDeclaration().get().canBeAssignedTo(this);
            }
        }

        return false;
    }

    @Override
    public boolean isTypeParameter() {
        return false;
    }

    @Override
    public ResolvedFieldDeclaration getField(String name) {
        return reflectionClassAdapter.getField(name);
    }

    @Override
    public List<ResolvedFieldDeclaration> getAllFields() {
        return reflectionClassAdapter.getAllFields();
    }

    @Override
    public SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {
        for (Field field : clazz.getFields()) {
            if (field.getName().equals(name)) {
                return SymbolReference.solved(new ReflectionFieldDeclaration(field, typeSolver));
            }
        }
        return SymbolReference.unsolved();
    }

    @Override
    public List<ResolvedReferenceType> getAncestors(boolean acceptIncompleteList) {
        // we do not attempt to perform any symbol solving when analyzing ancestors in the reflection model, so we can
        // simply ignore the boolean parameter here; an UnsolvedSymbolException cannot occur
        return reflectionClassAdapter.getAncestors();
    }

    @Override
    public Set<ResolvedMethodDeclaration> getDeclaredMethods() {
        return reflectionClassAdapter.getDeclaredMethods();
    }

    @Override
    public boolean hasField(String name) {
        return reflectionClassAdapter.hasField(name);
    }

    @Override
    public String getName() {
        return clazz.getSimpleName();
    }

    @Override
    public boolean isInterface() {
        return true;
    }

    @Override
    public List<ResolvedReferenceType> getInterfacesExtended() {
        List<ResolvedReferenceType> res = new ArrayList<>();
        for (Class i : clazz.getInterfaces()) {
            res.add(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(i, typeSolver)));
        }
        return res;
    }

    @Override
    public Optional<ResolvedReferenceTypeDeclaration> containerType() {
        return reflectionClassAdapter.containerType();
    }

    @Override
    public Set<ResolvedReferenceTypeDeclaration> internalTypes() {
        return Arrays.stream(this.clazz.getDeclaredClasses())
                .map(ic -> ReflectionFactory.typeDeclarationFor(ic, typeSolver))
                .collect(Collectors.toSet());
    }

    @Override
    public ResolvedInterfaceDeclaration asInterface() {
        return this;
    }

    @Override
    public boolean hasDirectlyAnnotation(String canonicalName) {
        return reflectionClassAdapter.hasDirectlyAnnotation(canonicalName);
    }

    @Override
    public List<ResolvedTypeParameterDeclaration> getTypeParameters() {
        return reflectionClassAdapter.getTypeParameters();
    }

    @Override
    public AccessSpecifier accessSpecifier() {
        return ReflectionFactory.modifiersToAccessLevel(this.clazz.getModifiers());
    }

    @Override
    public List<ResolvedConstructorDeclaration> getConstructors() {
        return Collections.emptyList();
    }
}
