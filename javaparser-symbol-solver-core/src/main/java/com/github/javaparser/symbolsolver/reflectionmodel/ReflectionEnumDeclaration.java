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
import com.github.javaparser.resolution.Context;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.logic.ConflictingGenericTypesException;
import com.github.javaparser.resolution.logic.InferenceContext;
import com.github.javaparser.resolution.logic.MethodResolutionCapability;
import com.github.javaparser.resolution.model.SymbolReference;
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
public class ReflectionEnumDeclaration extends AbstractTypeDeclaration
        implements ResolvedEnumDeclaration,
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
    /// Constructors
    ///

    public ReflectionEnumDeclaration(Class<?> clazz, TypeSolver typeSolver) {
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
        if (clazz.isLocalClass()) {
            throw new IllegalArgumentException("Class should not be a local class");
        }
        if (isRecordType(clazz)) {
            throw new IllegalArgumentException("Class should not be a record");
        }
        if (!clazz.isEnum()) {
            throw new IllegalArgumentException("Class should be an enum");
        }
        this.clazz = clazz;
        this.typeSolver = typeSolver;
        this.reflectionClassAdapter = new ReflectionClassAdapter(clazz, typeSolver, this);
    }

    ///
    /// Public methods
    ///

    @Override
    public AccessSpecifier accessSpecifier() {
        return ReflectionFactory.modifiersToAccessLevel(this.clazz.getModifiers());
    }

    @Override
    public Optional<ResolvedReferenceTypeDeclaration> containerType() {
        return reflectionClassAdapter.containerType();
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
    public List<ResolvedReferenceType> getAncestors(boolean acceptIncompleteList) {
        // we do not attempt to perform any symbol solving when analyzing ancestors in the reflection model, so we can
        // simply ignore the boolean parameter here; an UnsolvedSymbolException cannot occur
        return reflectionClassAdapter.getAncestors();
    }

    @Override
    public ResolvedFieldDeclaration getField(String name) {
        return reflectionClassAdapter.getField(name);
    }

    @Override
    public boolean hasField(String name) {
        return reflectionClassAdapter.hasField(name);
    }

    @Override
    public List<ResolvedFieldDeclaration> getAllFields() {
        return reflectionClassAdapter.getAllFields();
    }

    @Override
    public Set<ResolvedMethodDeclaration> getDeclaredMethods() {
        return reflectionClassAdapter.getDeclaredMethods();
    }

    @Override
    public boolean canBeAssignedTo(ResolvedReferenceTypeDeclaration other) {
        String otherName = other.getQualifiedName();
        // Enums cannot be extended
        if (otherName.equals(this.getQualifiedName())) {
            return true;
        }
        if (JAVA_LANG_ENUM.equals(otherName)) {
            return true;
        }
        // Enum implements Comparable and Serializable
        if (otherName.equals(JAVA_LANG_COMPARABLE)) {
            return true;
        }
        if (otherName.equals(JAVA_IO_SERIALIZABLE)) {
            return true;
        }
        return other.isJavaLangObject();
    }

    @Override
    public boolean isAssignableBy(ResolvedType type) {
        return reflectionClassAdapter.isAssignableBy(type);
    }

    @Override
    public boolean isAssignableBy(ResolvedReferenceTypeDeclaration other) {
        return isAssignableBy(new ReferenceTypeImpl(other));
    }

    @Override
    public boolean hasDirectlyAnnotation(String qualifiedName) {
        return reflectionClassAdapter.hasDirectlyAnnotation(qualifiedName);
    }

    @Override
    public String getName() {
        return clazz.getSimpleName();
    }

    @Override
    public List<ResolvedTypeParameterDeclaration> getTypeParameters() {
        return reflectionClassAdapter.getTypeParameters();
    }

    @Override
    public SymbolReference<ResolvedMethodDeclaration> solveMethod(
            String name, List<ResolvedType> parameterTypes, boolean staticOnly) {
        return ReflectionMethodResolutionLogic.solveMethod(name, parameterTypes, staticOnly, typeSolver, this, clazz);
    }

    @Override
    public Optional<MethodUsage> solveMethodAsUsage(
            String name,
            List<ResolvedType> parameterTypes,
            Context invokationContext,
            List<ResolvedType> typeParameterValues) {
        Optional<MethodUsage> res = ReflectionMethodResolutionLogic.solveMethodAsUsage(
                name, parameterTypes, typeSolver, invokationContext, typeParameterValues, this, clazz);
        if (res.isPresent()) {
            // We have to replace method type typeParametersValues here
            InferenceContext inferenceContext = new InferenceContext(typeSolver);
            MethodUsage methodUsage = res.get();
            int i = 0;
            List<ResolvedType> parameters = new LinkedList<>();
            for (ResolvedType actualType : parameterTypes) {
                ResolvedType formalType = methodUsage.getParamType(i);
                // We need to replace the class type typeParametersValues (while we derive the method ones)

                parameters.add(inferenceContext.addPair(formalType, actualType));
                i++;
            }
            try {
                ResolvedType returnType = inferenceContext.addSingle(methodUsage.returnType());
                for (int j = 0; j < parameters.size(); j++) {
                    methodUsage = methodUsage.replaceParamType(j, inferenceContext.resolve(parameters.get(j)));
                }
                methodUsage = methodUsage.replaceReturnType(inferenceContext.resolve(returnType));
                return Optional.of(methodUsage);
            } catch (ConflictingGenericTypesException e) {
                return Optional.empty();
            }
        } else {
            return res;
        }
    }

    @Override
    public SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {
        if (hasEnumConstant(name)) {
            ResolvedEnumConstantDeclaration enumConstant = getEnumConstant(name);
            return SymbolReference.solved(enumConstant);
        }
        return SymbolReference.unsolved();
    }

    @Override
    public List<ResolvedEnumConstantDeclaration> getEnumConstants() {
        return Arrays.stream(clazz.getFields())
                .filter(Field::isEnumConstant)
                .map(c -> new ReflectionEnumConstantDeclaration(c, typeSolver))
                .collect(Collectors.toList());
    }

    @Override
    public Set<ResolvedReferenceTypeDeclaration> internalTypes() {
        return Arrays.stream(this.clazz.getDeclaredClasses())
                .map(ic -> ReflectionFactory.typeDeclarationFor(ic, typeSolver))
                .collect(Collectors.toSet());
    }

    @Override
    public List<ResolvedConstructorDeclaration> getConstructors() {
        return reflectionClassAdapter.getConstructors();
    }
}
