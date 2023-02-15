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

import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.logic.FunctionalInterfaceLogic;
import com.github.javaparser.resolution.model.LambdaArgumentTypePlaceholder;
import com.github.javaparser.resolution.model.typesystem.NullType;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;

import java.lang.annotation.Annotation;
import java.lang.reflect.Field;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.TypeVariable;
import java.util.*;
import java.util.stream.Collectors;

/**
 * @author Federico Tomassetti
 */
class ReflectionClassAdapter {

    private Class<?> clazz;
    private TypeSolver typeSolver;
    private ResolvedReferenceTypeDeclaration typeDeclaration;

    public ReflectionClassAdapter(Class<?> clazz, TypeSolver typeSolver, ResolvedReferenceTypeDeclaration typeDeclaration) {
        this.clazz = clazz;
        this.typeSolver = typeSolver;
        this.typeDeclaration = typeDeclaration;
    }

    public Optional<ReferenceTypeImpl> getSuperClass() {
        if (clazz.getGenericSuperclass() == null) {
            // There isn't a super class (e.g. when this refers to java.lang.Object)
            return Optional.empty();
        }
        java.lang.reflect.Type superType = clazz.getGenericSuperclass();
        if (superType instanceof ParameterizedType) {
            ParameterizedType parameterizedType = (ParameterizedType) superType;
            List<ResolvedType> typeParameters = Arrays.stream(parameterizedType.getActualTypeArguments())
                    .map((t) -> ReflectionFactory.typeUsageFor(t, typeSolver))
                    .collect(Collectors.toList());
            return Optional.of(new ReferenceTypeImpl(new ReflectionClassDeclaration(clazz.getSuperclass(), typeSolver), typeParameters));
        }
        return Optional.of(new ReferenceTypeImpl(new ReflectionClassDeclaration(clazz.getSuperclass(), typeSolver)));
    }

    public List<ResolvedReferenceType> getInterfaces() {
        List<ResolvedReferenceType> interfaces = new ArrayList<>();
        for (java.lang.reflect.Type superInterface : clazz.getGenericInterfaces()) {
            if (superInterface instanceof ParameterizedType) {
                ParameterizedType parameterizedType = (ParameterizedType) superInterface;
                List<ResolvedType> typeParameters = Arrays.stream(parameterizedType.getActualTypeArguments())
                        .map((t) -> ReflectionFactory.typeUsageFor(t, typeSolver))
                        .collect(Collectors.toList());
                interfaces.add(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration((Class<?>) ((ParameterizedType) superInterface).getRawType(), typeSolver), typeParameters));
            } else {
                interfaces.add(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration((Class<?>) superInterface, typeSolver)));
            }
        }
        return interfaces;
    }

    public List<ResolvedReferenceType> getAncestors() {
        List<ResolvedReferenceType> ancestors = new LinkedList<>();
		if (typeDeclaration.isClass() && !Object.class.getCanonicalName().equals(clazz.getCanonicalName())) {
			if (getSuperClass().isPresent()) {
				ReferenceTypeImpl superClass = getSuperClass().get();
				ancestors.add(superClass);
			} else {
				// Inject the implicitly added extends java.lang.Object
				ReferenceTypeImpl object = new ReferenceTypeImpl(
						new ReflectionClassDeclaration(Object.class, typeSolver));
				ancestors.add(object);
			}
		}
        ancestors.addAll(getInterfaces());
        return ancestors;
    }

    public ResolvedFieldDeclaration getField(String name) {
        for (Field field : clazz.getDeclaredFields()) {
            if (field.getName().equals(name)) {
                return new ReflectionFieldDeclaration(field, typeSolver);
            }
        }
        for (ResolvedReferenceType ancestor : typeDeclaration.getAllAncestors()) {
            if (ancestor.getTypeDeclaration().isPresent()) {
                ResolvedReferenceTypeDeclaration typeDeclaration = ancestor.getTypeDeclaration().get();
                if (typeDeclaration.hasField(name)) {
                    ReflectionFieldDeclaration reflectionFieldDeclaration = (ReflectionFieldDeclaration) typeDeclaration.getField(name);
                    return reflectionFieldDeclaration.replaceType(ancestor.getFieldType(name).get());
                }
            }
        }
        throw new UnsolvedSymbolException(name, "Field in " + this);
    }

    public boolean hasField(String name) {
        // First consider fields declared on this class
        for (Field field : clazz.getDeclaredFields()) {
            if (field.getName().equals(name)) {
                return true;
            }
        }

        // Then consider fields inherited from ancestors
        for (ResolvedReferenceType ancestor : typeDeclaration.getAllAncestors()) {
            if (ancestor.getTypeDeclaration().isPresent() && ancestor.getTypeDeclaration().get().hasField(name)) {
                return true;
            }
        }

        return false;
    }

    public List<ResolvedFieldDeclaration> getAllFields() {
        ArrayList<ResolvedFieldDeclaration> fields = new ArrayList<>();

        // First consider fields declared on this class
        for (Field field : clazz.getDeclaredFields()) {
            fields.add(new ReflectionFieldDeclaration(field, typeSolver));
        }

        // Then consider fields inherited from ancestors
        for (ResolvedReferenceType ancestor : typeDeclaration.getAllAncestors()) {
            ancestor.getTypeDeclaration().ifPresent(ancestorTypeDeclaration -> {
                fields.addAll(ancestorTypeDeclaration.getAllFields());
            });
        }

        return fields;
    }

    public Set<ResolvedMethodDeclaration> getDeclaredMethods() {
        return Arrays.stream(clazz.getDeclaredMethods())
                .filter(m -> !m.isSynthetic() && !m.isBridge())
                .map(m -> new ReflectionMethodDeclaration(m, typeSolver))
                .collect(Collectors.toSet());
    }

    public List<ResolvedTypeParameterDeclaration> getTypeParameters() {
        List<ResolvedTypeParameterDeclaration> params = new ArrayList<>();
        for (TypeVariable<?> tv : this.clazz.getTypeParameters()) {
            params.add(new ReflectionTypeParameter(tv, true, typeSolver));
        }
        return params;
    }

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
        if (type.describe().equals(typeDeclaration.getQualifiedName())) {
            return true;
        }
        if (type instanceof ReferenceTypeImpl) {
            ReferenceTypeImpl otherTypeDeclaration = (ReferenceTypeImpl) type;
            if(otherTypeDeclaration.getTypeDeclaration().isPresent()) {
                return otherTypeDeclaration.getTypeDeclaration().get().canBeAssignedTo(typeDeclaration);
            }
        }

        return false;
    }

    public boolean hasDirectlyAnnotation(String canonicalName) {
        for (Annotation a : clazz.getDeclaredAnnotations()) {
            if (a.annotationType().getCanonicalName().equals(canonicalName)) {
                return true;
            }
        }
        return false;
    }

    private final boolean isFunctionalInterface() {
        return FunctionalInterfaceLogic.getFunctionalMethod(typeDeclaration).isPresent();
    }

    public List<ResolvedConstructorDeclaration> getConstructors() {
        return Arrays.stream(clazz.getDeclaredConstructors())
                .filter(m -> !m.isSynthetic())
                .map(m -> new ReflectionConstructorDeclaration(m, typeSolver))
                .collect(Collectors.toList());
    }
    
    public Optional<ResolvedReferenceTypeDeclaration> containerType() {
        Class<?> declaringClass = clazz.getDeclaringClass();
        return declaringClass == null ?
                Optional.empty() :
                Optional.of(ReflectionFactory.typeDeclarationFor(declaringClass, typeSolver));
    }
}
