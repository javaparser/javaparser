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

package com.github.javaparser.symbolsolver.reflectionmodel;

import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.core.resolution.MethodUsageResolutionCapability;
import com.github.javaparser.symbolsolver.javaparsermodel.LambdaArgumentTypePlaceholder;
import com.github.javaparser.symbolsolver.logic.AbstractTypeDeclaration;
import com.github.javaparser.symbolsolver.logic.ConfilictingGenericTypesException;
import com.github.javaparser.symbolsolver.logic.InferenceContext;
import com.github.javaparser.symbolsolver.logic.MethodResolutionCapability;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.NullType;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;

import java.lang.reflect.Field;
import java.util.*;
import java.util.stream.Collectors;

/**
 * @author Federico Tomassetti
 */
public class ReflectionInterfaceDeclaration extends AbstractTypeDeclaration
        implements ResolvedInterfaceDeclaration, MethodResolutionCapability, MethodUsageResolutionCapability {

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
        return isAssignableBy(new ReferenceTypeImpl(other, typeSolver));
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
    public SymbolReference<ResolvedMethodDeclaration> solveMethod(String name, List<ResolvedType> parameterTypes, boolean staticOnly) {
        return ReflectionMethodResolutionLogic.solveMethod(name, parameterTypes, staticOnly,
                typeSolver,this, clazz);
    }

    @Override
    public String toString() {
        return "ReflectionInterfaceDeclaration{" +
                "clazz=" + clazz.getCanonicalName() +
                '}';
    }

    public ResolvedType getUsage(Node node) {
        return new ReferenceTypeImpl(this, typeSolver);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof ReflectionInterfaceDeclaration)) return false;

        ReflectionInterfaceDeclaration that = (ReflectionInterfaceDeclaration) o;

        if (!clazz.getCanonicalName().equals(that.clazz.getCanonicalName())) return false;

        if (!getTypeParameters().equals(that.getTypeParameters())) {
            return false;
        }

        return true;
    }

    @Override
    public int hashCode() {
        return clazz.hashCode();
    }

    public Optional<MethodUsage> solveMethodAsUsage(String name, List<ResolvedType> parameterTypes,
                                                    Context invokationContext, List<ResolvedType> typeParameterValues) {
        Optional<MethodUsage> res = ReflectionMethodResolutionLogic.solveMethodAsUsage(name, parameterTypes, typeSolver, invokationContext,
                typeParameterValues, this, clazz);
        if (res.isPresent()) {
            // We have to replace method type typeParametersValues here
            InferenceContext inferenceContext = new InferenceContext(MyObjectProvider.INSTANCE);
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
                for (int j=0;j<parameters.size();j++) {
                    methodUsage = methodUsage.replaceParamType(j, inferenceContext.resolve(parameters.get(j)));
                }
                methodUsage = methodUsage.replaceReturnType(inferenceContext.resolve(returnType));
                return Optional.of(methodUsage);
            } catch (ConfilictingGenericTypesException e) {
                return Optional.empty();
            }
        } else {
            return res;
        }
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

        if (other.isJavaLangObject()) {
            // Everything can be assigned to {@code java.lang.Object}
            return true;
        }

        return false;
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
            if(otherTypeDeclaration.getTypeDeclaration().isPresent()) {
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

    @Deprecated
    public SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {
        for (Field field : clazz.getFields()) {
            if (field.getName().equals(name)) {
                return SymbolReference.solved(new ReflectionFieldDeclaration(field, typeSolver));
            }
        }
        return SymbolReference.unsolved(ResolvedValueDeclaration.class);
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
            res.add(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(i, typeSolver), typeSolver));
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

    @Override
    public Optional<ClassOrInterfaceDeclaration> toAst() {
        return Optional.empty();
    }
}
