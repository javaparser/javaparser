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
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.types.*;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.*;

import java.lang.reflect.GenericArrayType;
import java.lang.reflect.Modifier;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.WildcardType;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * @author Federico Tomassetti
 */
public class ReflectionFactory {

    public static ResolvedReferenceTypeDeclaration typeDeclarationFor(Class<?> clazz, TypeSolver typeSolver) {
        if (clazz.isArray()) {
            throw new IllegalArgumentException("No type declaration available for an Array");
        } else if (clazz.isPrimitive()) {
            throw new IllegalArgumentException();
        } else if (clazz.isAnnotation()) {
            return new ReflectionAnnotationDeclaration(clazz, typeSolver);
        } else if (clazz.isInterface()) {
            return new ReflectionInterfaceDeclaration(clazz, typeSolver);
        } else if (clazz.isEnum()) {
            return new ReflectionEnumDeclaration(clazz, typeSolver);
        } else {
            return new ReflectionClassDeclaration(clazz, typeSolver);
        }
    }

    public static ResolvedType typeUsageFor(java.lang.reflect.Type type, TypeSolver typeSolver) {
        if (type instanceof java.lang.reflect.TypeVariable) {
            java.lang.reflect.TypeVariable<?> tv = (java.lang.reflect.TypeVariable<?>) type;
            boolean declaredOnClass = tv.getGenericDeclaration() instanceof java.lang.reflect.Type;
            ResolvedTypeParameterDeclaration typeParameter = new ReflectionTypeParameter(tv, declaredOnClass, typeSolver);
            return new ResolvedTypeVariable(typeParameter);
        } else if (type instanceof ParameterizedType) {
            ParameterizedType pt = (ParameterizedType) type;
            ResolvedReferenceType rawType = typeUsageFor(pt.getRawType(), typeSolver).asReferenceType();
            List<java.lang.reflect.Type> actualTypes = new ArrayList<>();
            actualTypes.addAll(Arrays.asList(pt.getActualTypeArguments()));
            // we consume the actual types
            rawType = rawType.transformTypeParameters(tp -> typeUsageFor(actualTypes.remove(0), typeSolver)).asReferenceType();
            return rawType;
        } else if (type instanceof Class) {
            Class<?> c = (Class<?>) type;
            if (c.isPrimitive()) {
                if (c.getName().equals(Void.TYPE.getName())) {
                    return ResolvedVoidType.INSTANCE;
                } else {
                    return ResolvedPrimitiveType.byName(c.getName());
                }
            } else if (c.isArray()) {
                return new ResolvedArrayType(typeUsageFor(c.getComponentType(), typeSolver));
            } else {
                return new ReferenceTypeImpl(typeDeclarationFor(c, typeSolver), typeSolver);
            }
        } else if (type instanceof GenericArrayType) {
            GenericArrayType genericArrayType = (GenericArrayType) type;
            return new ResolvedArrayType(typeUsageFor(genericArrayType.getGenericComponentType(), typeSolver));
        } else if (type instanceof WildcardType) {
            WildcardType wildcardType = (WildcardType) type;
            if (wildcardType.getLowerBounds().length > 0 && wildcardType.getUpperBounds().length > 0) {
                if (wildcardType.getUpperBounds().length == 1 && wildcardType.getUpperBounds()[0].getTypeName().equals("java.lang.Object")) {
                    // ok, it does not matter
                }
            }
            if (wildcardType.getLowerBounds().length > 0) {
                if (wildcardType.getLowerBounds().length > 1) {
                    throw new UnsupportedOperationException();
                }
                return ResolvedWildcard.superBound(typeUsageFor(wildcardType.getLowerBounds()[0], typeSolver));
            }
            if (wildcardType.getUpperBounds().length > 0) {
                if (wildcardType.getUpperBounds().length > 1) {
                    throw new UnsupportedOperationException();
                }
                return ResolvedWildcard.extendsBound(typeUsageFor(wildcardType.getUpperBounds()[0], typeSolver));
            }
            return ResolvedWildcard.UNBOUNDED;
        } else {
            throw new UnsupportedOperationException(type.getClass().getCanonicalName() + " " + type);
        }
    }

    static AccessSpecifier modifiersToAccessLevel(final int modifiers) {
        if (Modifier.isPublic(modifiers)) {
            return AccessSpecifier.PUBLIC;
        } else if (Modifier.isProtected(modifiers)) {
            return AccessSpecifier.PROTECTED;
        } else if (Modifier.isPrivate(modifiers)) {
            return AccessSpecifier.PRIVATE;
        } else {
            return AccessSpecifier.PACKAGE_PRIVATE;
        }
    }
}
