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
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.*;

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
    
    private static String JAVA_LANG_OBJECT = Object.class.getCanonicalName();

    public static ResolvedReferenceTypeDeclaration typeDeclarationFor(Class<?> clazz, TypeSolver typeSolver) {
        if (clazz.isArray()) {
            throw new IllegalArgumentException("No type declaration available for an Array");
        }
            if (clazz.isPrimitive()) {
            throw new IllegalArgumentException();
        }
            if (clazz.isAnnotation()) {
            return new ReflectionAnnotationDeclaration(clazz, typeSolver);
        }
            if (clazz.isInterface()) {
            return new ReflectionInterfaceDeclaration(clazz, typeSolver);
        }
            if (clazz.isEnum()) {
            return new ReflectionEnumDeclaration(clazz, typeSolver);
        }
        return new ReflectionClassDeclaration(clazz, typeSolver);
    }

    public static ResolvedType typeUsageFor(java.lang.reflect.Type type, TypeSolver typeSolver) {
        if (type instanceof java.lang.reflect.TypeVariable) {
            java.lang.reflect.TypeVariable<?> tv = (java.lang.reflect.TypeVariable<?>) type;
            boolean declaredOnClass = tv.getGenericDeclaration() instanceof java.lang.reflect.Type;
            ResolvedTypeParameterDeclaration typeParameter = new ReflectionTypeParameter(tv, declaredOnClass, typeSolver);
            return new ResolvedTypeVariable(typeParameter);
        }
            if (type instanceof ParameterizedType) {
            ParameterizedType pt = (ParameterizedType) type;
            ResolvedReferenceType rawType = typeUsageFor(pt.getRawType(), typeSolver).asReferenceType();
            List<java.lang.reflect.Type> actualTypes = new ArrayList<>();
            actualTypes.addAll(Arrays.asList(pt.getActualTypeArguments()));
            // we consume the actual types
            rawType = rawType.transformTypeParameters(tp -> typeUsageFor(actualTypes.remove(0), typeSolver)).asReferenceType();
            return rawType;
        }
            if (type instanceof Class) {
            Class<?> c = (Class<?>) type;
            if (c.isPrimitive()) {
                if (c.getName().equals(Void.TYPE.getName())) {
                    return ResolvedVoidType.INSTANCE;
                }
                return ResolvedPrimitiveType.byName(c.getName());
            }
                    if (c.isArray()) {
                return new ResolvedArrayType(typeUsageFor(c.getComponentType(), typeSolver));
            }
            return new ReferenceTypeImpl(typeDeclarationFor(c, typeSolver));
        }
            if (type instanceof GenericArrayType) {
            GenericArrayType genericArrayType = (GenericArrayType) type;
            return new ResolvedArrayType(typeUsageFor(genericArrayType.getGenericComponentType(), typeSolver));
        }
            if (type instanceof WildcardType) {
            WildcardType wildcardType = (WildcardType) type;
            if (wildcardType.getLowerBounds().length > 0 && wildcardType.getUpperBounds().length > 0) {
                if (wildcardType.getUpperBounds().length == 1 && wildcardType.getUpperBounds()[0].getTypeName().equals(JAVA_LANG_OBJECT)) {
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
        }
        throw new UnsupportedOperationException(type.getClass().getCanonicalName() + " " + type);
    }

    static AccessSpecifier modifiersToAccessLevel(final int modifiers) {
        if (Modifier.isPublic(modifiers)) {
            return AccessSpecifier.PUBLIC;
        }
            if (Modifier.isProtected(modifiers)) {
            return AccessSpecifier.PROTECTED;
        }
            if (Modifier.isPrivate(modifiers)) {
            return AccessSpecifier.PRIVATE;
        }
        return AccessSpecifier.NONE;
    }
}
