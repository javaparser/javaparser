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

package com.github.javaparser.symbolsolver.reflectionmodel;

import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.resolution.Context;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.logic.MethodResolutionLogic;
import com.github.javaparser.resolution.model.LambdaArgumentTypePlaceholder;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.core.resolution.MethodUsageResolutionCapability;
import com.github.javaparser.symbolsolver.core.resolution.SymbolResolutionCapability;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.ContextHelper;
import com.github.javaparser.symbolsolver.logic.AbstractClassDeclaration;
import com.github.javaparser.symbolsolver.reflectionmodel.comparators.MethodComparator;

import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.*;
import java.util.function.Predicate;
import java.util.stream.Collectors;

/**
 * @author Federico Tomassetti
 */
public class ReflectionClassDeclaration extends AbstractClassDeclaration
        implements MethodUsageResolutionCapability, SymbolResolutionCapability {

    ///
    /// Fields
    ///

    private Class<?> clazz;
    private TypeSolver typeSolver;
    private ReflectionClassAdapter reflectionClassAdapter;

    ///
    /// Constructors
    ///

    public ReflectionClassDeclaration(Class<?> clazz, TypeSolver typeSolver) {
        if (clazz == null) {
            throw new IllegalArgumentException("Class should not be null");
        }
        if (clazz.isInterface()) {
            throw new IllegalArgumentException("Class should not be an interface");
        }
        if (clazz.isPrimitive()) {
            throw new IllegalArgumentException("Class should not represent a primitive class");
        }
        if (clazz.isArray()) {
            throw new IllegalArgumentException("Class should not be an array");
        }
        if (clazz.isEnum()) {
            throw new IllegalArgumentException("Class should not be an enum");
        }
        this.clazz = clazz;
        this.typeSolver = typeSolver;
        this.reflectionClassAdapter = new ReflectionClassAdapter(clazz, typeSolver, this);
    }

    ///
    /// Public methods
    ///

    @Override
    public Set<ResolvedMethodDeclaration> getDeclaredMethods() {
        return reflectionClassAdapter.getDeclaredMethods();
    }

    @Override
    public List<ResolvedReferenceType> getAncestors(boolean acceptIncompleteList) {
        // we do not attempt to perform any symbol solving when analyzing ancestors in the reflection model, so we can
        // simply ignore the boolean parameter here; an UnsolvedSymbolException cannot occur
        return reflectionClassAdapter.getAncestors();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        ReflectionClassDeclaration that = (ReflectionClassDeclaration) o;

        if (!clazz.getCanonicalName().equals(that.clazz.getCanonicalName())) return false;

        return true;
    }

    @Override
    public int hashCode() {
        return clazz.hashCode();
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
            return canonicalName.substring(getPackageName().length() + 1, canonicalName.length());
        }
        return null;
    }

    @Override
    public String getQualifiedName() {
        return clazz.getCanonicalName();
    }

    @Override
    @Deprecated
    public SymbolReference<ResolvedMethodDeclaration> solveMethod(String name, List<ResolvedType> argumentsTypes, boolean staticOnly) {
        Predicate<Method> staticFilter = m -> !staticOnly || (staticOnly && Modifier.isStatic(m.getModifiers()));

        List<ResolvedMethodDeclaration> candidateSolvedMethods = new ArrayList<>();

        // First consider the directly-declared methods.
        List<Method> methods = Arrays.stream(clazz.getDeclaredMethods())
                .filter(m -> m.getName().equals(name))
                .filter(staticFilter)
                .filter(method -> !method.isBridge())
                .filter(method -> !method.isSynthetic())
                .sorted(new MethodComparator())
                .collect(Collectors.toList());

        // Transform into resolved method declarations
        for (Method method : methods) {
            ResolvedMethodDeclaration methodDeclaration = new ReflectionMethodDeclaration(method, typeSolver);
            candidateSolvedMethods.add(methodDeclaration);

            // no need to search for overloaded/inherited candidateSolvedMethods if the method has no parameters
            if (argumentsTypes.isEmpty() && methodDeclaration.getNumberOfParams() == 0) {
                return SymbolReference.solved(methodDeclaration);
            }
        }

        // Next consider methods declared within extended superclasses.
        getSuperClass()
                .flatMap(ResolvedReferenceType::getTypeDeclaration)
                .ifPresent(superClassTypeDeclaration -> {
                    SymbolReference<ResolvedMethodDeclaration> ref = MethodResolutionLogic.solveMethodInType(superClassTypeDeclaration, name, argumentsTypes, staticOnly);
                    if (ref.isSolved()) {
                        candidateSolvedMethods.add(ref.getCorrespondingDeclaration());
                    }
                });

        // Next consider methods declared within implemented interfaces.
        for (ResolvedReferenceType interfaceDeclaration : getInterfaces()) {
            interfaceDeclaration.getTypeDeclaration()
                    .ifPresent(interfaceTypeDeclaration -> {
                        SymbolReference<ResolvedMethodDeclaration> ref = MethodResolutionLogic.solveMethodInType(interfaceTypeDeclaration, name, argumentsTypes, staticOnly);
                        if (ref.isSolved()) {
                            candidateSolvedMethods.add(ref.getCorrespondingDeclaration());
                        }
                    });
        }

        // When empty there is no sense in trying to find the most applicable.
        // This is useful for debugging. Performance is not affected as 
        // MethodResolutionLogic.findMostApplicable method returns very early 
        // when candidateSolvedMethods is empty.
        if (candidateSolvedMethods.isEmpty()) {
            return SymbolReference.unsolved();
        }
        return MethodResolutionLogic.findMostApplicable(candidateSolvedMethods, name, argumentsTypes, typeSolver);
    }

    @Override
    public String toString() {
        return "ReflectionClassDeclaration{" +
                "clazz=" + getId() +
                '}';
    }

    public ResolvedType getUsage(Node node) {

        return new ReferenceTypeImpl(this);
    }

    public Optional<MethodUsage> solveMethodAsUsage(String name, List<ResolvedType> argumentsTypes, Context invokationContext, List<ResolvedType> typeParameterValues) {
        List<MethodUsage> methodUsages = new ArrayList<>();

        List<Method> allMethods = Arrays.stream(clazz.getDeclaredMethods())
                .filter((m) -> m.getName().equals(name))
                .sorted(new MethodComparator())
                .collect(Collectors.toList());

        for (Method method : allMethods) {
            if (method.isBridge() || method.isSynthetic()) {
                continue;
            }
            ResolvedMethodDeclaration methodDeclaration = new ReflectionMethodDeclaration(method, typeSolver);
            MethodUsage methodUsage = new MethodUsage(methodDeclaration);
            for (int i = 0; i < getTypeParameters().size() && i < typeParameterValues.size(); i++) {
                ResolvedTypeParameterDeclaration tpToReplace = getTypeParameters().get(i);
                ResolvedType newValue = typeParameterValues.get(i);
                methodUsage = methodUsage.replaceTypeParameter(tpToReplace, newValue);
            }
            methodUsages.add(methodUsage);

            // no need to search for overloaded/inherited methodUsages if the method has no parameters
            if (argumentsTypes.isEmpty() && methodUsage.getNoParams() == 0) {
                return Optional.of(methodUsage);
            }
        }

        getSuperClass().ifPresent(superClass -> {
            superClass.getTypeDeclaration().ifPresent(superClassTypeDeclaration -> {
                ContextHelper.solveMethodAsUsage(superClassTypeDeclaration, name, argumentsTypes, invokationContext, typeParameterValues)
                        .ifPresent(methodUsages::add);
            });
        });

        for (ResolvedReferenceType interfaceDeclaration : getInterfaces()) {
            interfaceDeclaration.getTypeDeclaration()
                    .flatMap(superClassTypeDeclaration -> interfaceDeclaration.getTypeDeclaration())
                    .flatMap(interfaceTypeDeclaration -> ContextHelper.solveMethodAsUsage(interfaceTypeDeclaration, name, argumentsTypes, invokationContext, typeParameterValues))
                    .ifPresent(methodUsages::add);
        }
        Optional<MethodUsage> ref = MethodResolutionLogic.findMostApplicableUsage(methodUsages, name, argumentsTypes, typeSolver);
        return ref;
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
                && new ReflectionClassDeclaration(clazz.getSuperclass(), typeSolver).canBeAssignedTo(other)) {
            return true;
        }
        for (Class<?> interfaze : clazz.getInterfaces()) {
            if (new ReflectionInterfaceDeclaration(interfaze, typeSolver).canBeAssignedTo(other)) {
                return true;
            }
        }

        return false;
    }

    @Override
    public boolean isAssignableBy(ResolvedType type) {
        return reflectionClassAdapter.isAssignableBy(type);
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
    public boolean hasDirectlyAnnotation(String canonicalName) {
        return reflectionClassAdapter.hasDirectlyAnnotation(canonicalName);
    }

    @Override
    public boolean hasField(String name) {
        return reflectionClassAdapter.hasField(name);
    }

    @Override
    public boolean isAssignableBy(ResolvedReferenceTypeDeclaration other) {
        return isAssignableBy(new ReferenceTypeImpl(other));
    }

    @Override
    public String getName() {
        return clazz.getSimpleName();
    }

    @Override
    public boolean isField() {
        return false;
    }

    @Override
    public boolean isParameter() {
        return false;
    }

    @Override
    public boolean isType() {
        return true;
    }

    @Override
    public boolean isClass() {
        return !clazz.isInterface();
    }

    @Override
    public Optional<ResolvedReferenceType> getSuperClass() {
        if(!reflectionClassAdapter.getSuperClass().isPresent()) {
            return Optional.empty();
        }
        return Optional.of(reflectionClassAdapter.getSuperClass().get());
    }

    @Override
    public List<ResolvedReferenceType> getInterfaces() {
        return reflectionClassAdapter.getInterfaces();
    }

    @Override
    public boolean isInterface() {
        return clazz.isInterface();
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
        return reflectionClassAdapter.getConstructors();
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

    ///
    /// Protected methods
    ///

    @Override
    protected ResolvedReferenceType object() {
        return new ReferenceTypeImpl(typeSolver.getSolvedJavaLangObject());
    }
}
