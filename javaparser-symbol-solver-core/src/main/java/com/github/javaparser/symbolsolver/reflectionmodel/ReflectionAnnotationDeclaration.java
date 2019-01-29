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

import com.github.javaparser.ast.body.AnnotationDeclaration;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.logic.AbstractTypeDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * @author Malte Skoruppa
 */
public class ReflectionAnnotationDeclaration extends AbstractTypeDeclaration implements ResolvedAnnotationDeclaration {

    ///
    /// Fields
    ///

    private Class<?> clazz;
    private TypeSolver typeSolver;
    private ReflectionClassAdapter reflectionClassAdapter;

    ///
    /// Constructor
    ///

    public ReflectionAnnotationDeclaration(Class<?> clazz, TypeSolver typeSolver) {
        if (!clazz.isAnnotation()) {
            throw new IllegalArgumentException("The given type is not an annotation.");
        }

        this.clazz = clazz;
        this.typeSolver = typeSolver;
        this.reflectionClassAdapter = new ReflectionClassAdapter(clazz, typeSolver, this);
    }

    ///
    /// Public methods
    ///

    @Override
    public String getPackageName() {
        if (clazz.getPackage() != null) {
            return clazz.getPackage().getName();
        }
        return "";
    }

    @Override
    public String getClassName() {
        String qualifiedName = getQualifiedName();
        if(qualifiedName.contains(".")) {
            return qualifiedName.substring(qualifiedName.lastIndexOf("."), qualifiedName.length());
        } else {
            return qualifiedName;
        }
    }

    @Override
    public String getQualifiedName() {
        return clazz.getCanonicalName();
    }

    @Override
    public String toString() {
        return getClass().getSimpleName() + "{" +
               "clazz=" + clazz.getCanonicalName() +
               '}';
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof ReflectionAnnotationDeclaration)) return false;

        ReflectionAnnotationDeclaration that = (ReflectionAnnotationDeclaration) o;

        return clazz.getCanonicalName().equals(that.clazz.getCanonicalName());
    }

    @Override
    public int hashCode() {
        return clazz.getCanonicalName().hashCode();
    }

    @Override
    public boolean isAssignableBy(ResolvedType type) {
        // TODO #1836
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isAssignableBy(ResolvedReferenceTypeDeclaration other) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean hasDirectlyAnnotation(String canonicalName) {
        return reflectionClassAdapter.hasDirectlyAnnotation(canonicalName);
    }

    @Override
    public List<ResolvedFieldDeclaration> getAllFields() {
        // TODO #1837
        throw new UnsupportedOperationException();
    }

    @Override
    public List<ResolvedReferenceType> getAncestors(boolean acceptIncompleteList) {
        throw new UnsupportedOperationException();
    }

    @Override
    public Set<ResolvedMethodDeclaration> getDeclaredMethods() {
        // TODO #1838
        throw new UnsupportedOperationException();
    }

    @Override
    public String getName() {
        return clazz.getSimpleName();
    }

    @Override
    public Optional<ResolvedReferenceTypeDeclaration> containerType() {
        // TODO #1841
        throw new UnsupportedOperationException("containerType() is not supported for " + this.getClass().getCanonicalName());
    }

    /**
     * Annotation declarations cannot have type parameters and hence this method always returns an empty list.
     *
     * @return An empty list.
     */
    @Override
    public List<ResolvedTypeParameterDeclaration> getTypeParameters() {
        // Annotation declarations cannot have type parameters - i.e. we can always return an empty list.
        return Collections.emptyList();
    }

    @Override
    public List<ResolvedConstructorDeclaration> getConstructors() {
        return Collections.emptyList();
    }

    @Override
    public List<ResolvedAnnotationMemberDeclaration> getAnnotationMembers() {
        return Stream.of(clazz.getDeclaredMethods())
                       .map(m -> new ReflectionAnnotationMemberDeclaration(m, typeSolver))
                       .collect(Collectors.toList());
    }

    @Override
    public Optional<AnnotationDeclaration> toAst() {
        return Optional.empty();
    }
}
