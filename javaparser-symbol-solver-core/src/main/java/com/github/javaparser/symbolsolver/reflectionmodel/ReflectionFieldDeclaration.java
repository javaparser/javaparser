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
import com.github.javaparser.resolution.declarations.ResolvedAnnotation;
import com.github.javaparser.resolution.declarations.ResolvedAnnotationDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedFieldDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.utils.ModifierUtils;
import com.github.javaparser.symbolsolver.utils.ResolvedAnnotationsUtil;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.List;
import java.util.Optional;
import java.util.Set;

/**
 * @author Federico Tomassetti
 */
public class ReflectionFieldDeclaration implements ResolvedFieldDeclaration {

    private Field field;
    private TypeSolver typeSolver;
    private ResolvedType type;

    public ReflectionFieldDeclaration(Field field, TypeSolver typeSolver) {
        this.field = field;
        this.typeSolver = typeSolver;
        this.type = calcType();
    }

    private ReflectionFieldDeclaration(Field field, TypeSolver typeSolver, ResolvedType type) {
        this.field = field;
        this.typeSolver = typeSolver;
        this.type = type;
    }

    @Override
    public ResolvedType getType() {
        return type;
    }

    private ResolvedType calcType() {
        // TODO consider interfaces, enums, primitive types, arrays
        return ReflectionFactory.typeUsageFor(field.getGenericType(), typeSolver);
    }

    @Override
    public String getName() {
        return field.getName();
    }

    @Override
    public boolean isStatic() {
        return Modifier.isStatic(field.getModifiers());
    }
    
    @Override
    public boolean isVolatile() {
        return Modifier.isVolatile(field.getModifiers());
    }

    @Override
    public boolean isField() {
        return true;
    }

    @Override
    public ResolvedTypeDeclaration declaringType() {
        return ReflectionFactory.typeDeclarationFor(field.getDeclaringClass(), typeSolver);
    }

    public ResolvedFieldDeclaration replaceType(ResolvedType fieldType) {
        return new ReflectionFieldDeclaration(field, typeSolver, fieldType);
    }

    @Override
    public boolean isParameter() {
        return false;
    }

    @Override
    public boolean isType() {
        return false;
    }

    @Override
    public AccessSpecifier accessSpecifier() {
        return ReflectionFactory.modifiersToAccessLevel(field.getModifiers());
    }

    @Override
    public boolean hasModifier(com.github.javaparser.ast.Modifier.Keyword keyword) {
        return ModifierUtils.hasModifier(field, field.getModifiers(), keyword);
    }

    @Override
    public Optional<Object> constantValue() {
        Object tempValue = null;
        if (Modifier.isFinal(field.getModifiers()) && Modifier.isStatic(field.getModifiers())) {
            try {
                tempValue = tryGet(field::getBoolean);
                if(tempValue == null) {
                    tempValue = tryGet(field::getInt);
                }
                if(tempValue == null) {
                    tempValue = tryGet(field::getLong);
                }
                if(tempValue == null) {
                    tempValue = tryGet(field::getDouble);
                }
                if(tempValue == null) {
                    tempValue = tryGet(field::getFloat);
                }
                if(tempValue == null) {
                    tempValue = tryGet(field::get);
                    if(!(tempValue instanceof String)) {
                        tempValue = null;
                    }
                }
            } catch (Throwable ignore) {

            }
        }
        return Optional.ofNullable(tempValue);
    }

    @Override
    public List<? extends ResolvedAnnotation> getAnnotations() {
        return ResolvedAnnotationsUtil.getAnnotations(field, typeSolver);
    }

    @Override
    public Set<ResolvedAnnotationDeclaration> getDeclaredAnnotations() {
        return ResolvedAnnotationsUtil.getDeclaredAnnotations(field, typeSolver);
    }

    private Object tryGet(EFunction<Object, Object, Throwable> function) {
        try {
            return function.apply(null);
        } catch (Throwable ignore) {
            return null;
        }
    }

    private interface EFunction<P, R, T extends Throwable> {
        R apply(P param) throws T;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        ReflectionFieldDeclaration that = (ReflectionFieldDeclaration) o;

        if (!field.equals(that.field)) return false;

        return true;
    }

    @Override
    public int hashCode() {
        return field.hashCode();
    }
}
