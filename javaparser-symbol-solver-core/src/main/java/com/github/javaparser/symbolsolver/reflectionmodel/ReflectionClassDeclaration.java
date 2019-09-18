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

package com.github.javaparser.symbolsolver.reflectionmodel;

import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.core.resolution.MethodUsageResolutionCapability;
import com.github.javaparser.symbolsolver.javaparsermodel.LambdaArgumentTypePlaceholder;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.ContextHelper;
import com.github.javaparser.symbolsolver.logic.AbstractClassDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.symbolsolver.reflectionmodel.comparators.MethodComparator;
import com.github.javaparser.symbolsolver.resolution.MethodResolutionLogic;

import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.*;
import java.util.function.Predicate;
import java.util.stream.Collectors;

/**
 * @author Federico Tomassetti
 */
public class ReflectionClassDeclaration extends AbstractClassDeclaration implements MethodUsageResolutionCapability {

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
        List<ResolvedMethodDeclaration> methods = new ArrayList<>();
        Predicate<Method> staticFilter = m -> !staticOnly || (staticOnly && Modifier.isStatic(m.getModifiers()));
        for (Method method : Arrays.stream(clazz.getDeclaredMethods()).filter((m) -> m.getName().equals(name)).filter(staticFilter)
                                    .sorted(new MethodComparator()).collect(Collectors.toList())) {
            if (method.isBridge() || method.isSynthetic()) continue;
            ResolvedMethodDeclaration methodDeclaration = new ReflectionMethodDeclaration(method, typeSolver);
            methods.add(methodDeclaration);

            // no need to search for overloaded/inherited methods if the method has no parameters
            if (argumentsTypes.isEmpty() && methodDeclaration.getNumberOfParams() == 0) {
                return SymbolReference.solved(methodDeclaration);
            }
        }
        if (getSuperClass() != null) {
            ResolvedClassDeclaration superClass = (ResolvedClassDeclaration) getSuperClass().getTypeDeclaration();
            SymbolReference<ResolvedMethodDeclaration> ref = MethodResolutionLogic.solveMethodInType(superClass, name, argumentsTypes, staticOnly);
            if (ref.isSolved()) {
                methods.add(ref.getCorrespondingDeclaration());
            }
        }
        for (ResolvedReferenceType interfaceDeclaration : getInterfaces()) {
            SymbolReference<ResolvedMethodDeclaration> ref = MethodResolutionLogic.solveMethodInType(interfaceDeclaration.getTypeDeclaration(), name, argumentsTypes, staticOnly);
            if (ref.isSolved()) {
                methods.add(ref.getCorrespondingDeclaration());
            }
        }
        // When empty there is no sense in trying to find the most applicable.
        // This is useful for debugging. Performance is not affected as 
        // MethodResolutionLogic.findMostApplicable method returns very early 
        // when methods is empty.
        if (methods.isEmpty()) {
            return SymbolReference.unsolved(ResolvedMethodDeclaration.class);
        }
        return MethodResolutionLogic.findMostApplicable(methods, name, argumentsTypes, typeSolver);
    }

    @Override
    public String toString() {
        return "ReflectionClassDeclaration{" +
                "clazz=" + getId() +
                '}';
    }

    public ResolvedType getUsage(Node node) {

        return new ReferenceTypeImpl(this, typeSolver);
    }

    public Optional<MethodUsage> solveMethodAsUsage(String name, List<ResolvedType> argumentsTypes, Context invokationContext, List<ResolvedType> typeParameterValues) {
        List<MethodUsage> methods = new ArrayList<>();
        for (Method method : Arrays.stream(clazz.getDeclaredMethods()).filter((m) -> m.getName().equals(name)).sorted(new MethodComparator()).collect(Collectors.toList())) {
            if (method.isBridge() || method.isSynthetic()) continue;
            ResolvedMethodDeclaration methodDeclaration = new ReflectionMethodDeclaration(method, typeSolver);
            MethodUsage methodUsage = new MethodUsage(methodDeclaration);
            for (int i = 0; i < getTypeParameters().size() && i < typeParameterValues.size(); i++) {
                ResolvedTypeParameterDeclaration tpToReplace = getTypeParameters().get(i);
                ResolvedType newValue = typeParameterValues.get(i);
                methodUsage = methodUsage.replaceTypeParameter(tpToReplace, newValue);
            }
            methods.add(methodUsage);

            // no need to search for overloaded/inherited methods if the method has no parameters
            if (argumentsTypes.isEmpty() && methodUsage.getNoParams() == 0) {
                return Optional.of(methodUsage);
            }
        }
        if (getSuperClass() != null) {
            ResolvedClassDeclaration superClass = (ResolvedClassDeclaration) getSuperClass().getTypeDeclaration();
            Optional<MethodUsage> ref = ContextHelper.solveMethodAsUsage(superClass, name, argumentsTypes, invokationContext, typeParameterValues);
            if (ref.isPresent()) {
                methods.add(ref.get());
            }
        }
        for (ResolvedReferenceType interfaceDeclaration : getInterfaces()) {
            Optional<MethodUsage> ref = ContextHelper.solveMethodAsUsage(interfaceDeclaration.getTypeDeclaration(), name, argumentsTypes, invokationContext, typeParameterValues);
            if (ref.isPresent()) {
                methods.add(ref.get());
            }
        }
        Optional<MethodUsage> ref = MethodResolutionLogic.findMostApplicableUsage(methods, name, argumentsTypes, typeSolver);
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
    public boolean hasDirectlyAnnotation(String canonicalName) {
        return reflectionClassAdapter.hasDirectlyAnnotation(canonicalName);
    }

    @Override
    public boolean hasField(String name) {
        return reflectionClassAdapter.hasField(name);
    }

    @Override
    public boolean isAssignableBy(ResolvedReferenceTypeDeclaration other) {
        return isAssignableBy(new ReferenceTypeImpl(other, typeSolver));
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
    public ReferenceTypeImpl getSuperClass() {
        return reflectionClassAdapter.getSuperClass();
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

    @Override
    public Optional<Node> toAst() {
        return Optional.empty();
    }

    ///
    /// Protected methods
    ///

    @Override
    protected ResolvedReferenceType object() {
        return new ReferenceTypeImpl(typeSolver.solveType(Object.class.getCanonicalName()), typeSolver);
    }
}
