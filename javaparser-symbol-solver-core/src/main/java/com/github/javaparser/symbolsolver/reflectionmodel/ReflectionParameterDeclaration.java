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

import com.github.javaparser.resolution.declarations.ResolvedParameterDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;

import java.util.Objects;

/**
 * @author Federico Tomassetti
 */
public class ReflectionParameterDeclaration implements ResolvedParameterDeclaration {
    private Class<?> type;
    private java.lang.reflect.Type genericType;
    private TypeSolver typeSolver;
    private boolean variadic;
    private String name;

    /**
     *
     * @param type
     * @param genericType
     * @param typeSolver
     * @param variadic
     * @param name can potentially be null
     */
    public ReflectionParameterDeclaration(Class<?> type, java.lang.reflect.Type genericType, TypeSolver typeSolver,
                                          boolean variadic, String name) {
        this.type = type;
        this.genericType = genericType;
        this.typeSolver = typeSolver;
        this.variadic = variadic;
        this.name = name;
    }

    /**
     *
     * @return the name, which can be potentially null
     */
    @Override
    public String getName() {
        return name;
    }

    @Override
    public boolean hasName() {
        return name != null;
    }

    @Override
    public String toString() {
        return "ReflectionParameterDeclaration{" +
                "type=" + type +
                ", name=" + name +
                '}';
    }

    @Override
    public boolean isField() {
        return false;
    }

    @Override
    public boolean isParameter() {
        return true;
    }

    @Override
    public boolean isVariadic() {
        return variadic;
    }

    @Override
    public boolean isType() {
        return false;
    }

    @Override
    public ResolvedType getType() {
        return ReflectionFactory.typeUsageFor(genericType, typeSolver);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        ReflectionParameterDeclaration that = (ReflectionParameterDeclaration) o;
        return variadic == that.variadic &&
                Objects.equals(type, that.type) &&
                Objects.equals(genericType, that.genericType) &&
                Objects.equals(typeSolver, that.typeSolver) &&
                Objects.equals(name, that.name);
    }

    @Override
    public int hashCode() {
        return Objects.hash(type, genericType, typeSolver, variadic, name);
    }
}
