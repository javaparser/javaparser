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

import com.github.javaparser.symbolsolver.logic.AbstractTypeDeclaration;
import com.github.javaparser.symbolsolver.model.declarations.*;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceType;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.symbolsolver.model.typesystem.Type;

import java.util.List;
import java.util.Set;

/**
 * @author Federico Tomassetti
 */
public class ReflectionEnumDeclaration extends AbstractTypeDeclaration implements EnumDeclaration {

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
    public AccessLevel accessLevel() {
        return ReflectionFactory.modifiersToAccessLevel(this.clazz.getModifiers());
    }

    @Override
    public String getQualifiedName() {
        return clazz.getCanonicalName();
    }

    @Override
    public List<ReferenceType> getAncestors() {
        return reflectionClassAdapter.getAncestors();
    }

    @Override
    public FieldDeclaration getField(String name) {
        return reflectionClassAdapter.getField(name);
    }

    @Override
    public boolean hasField(String name) {
        return reflectionClassAdapter.hasField(name);
    }

    @Override
    public List<FieldDeclaration> getAllFields() {
        return reflectionClassAdapter.getAllFields();
    }

    @Override
    public Set<MethodDeclaration> getDeclaredMethods() {
        return reflectionClassAdapter.getDeclaredMethods();
    }

    @Override
    public boolean isAssignableBy(Type type) {
        return reflectionClassAdapter.isAssignableBy(type);
    }

    @Override
    public boolean isAssignableBy(TypeDeclaration other) {
        return isAssignableBy(new ReferenceTypeImpl(other, typeSolver));
    }

    @Override
    public boolean hasDirectlyAnnotation(String qualifiedName) {
        throw new UnsupportedOperationException();
    }

    @Override
    public String getName() {
        return clazz.getSimpleName();
    }

    @Override
    public List<TypeParameterDeclaration> getTypeParameters() {
        return reflectionClassAdapter.getTypeParameters();
    }
}
