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
import com.github.javaparser.resolution.declarations.ResolvedFieldDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;

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
}
