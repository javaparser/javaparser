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

package com.github.javaparser.symbolsolver.javassistmodel;

import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedParameterDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import javassist.CtClass;

/**
 * @author Federico Tomassetti
 */
public class JavassistParameterDeclaration implements ResolvedParameterDeclaration {
    private ResolvedType type;
    private TypeSolver typeSolver;
    private boolean variadic;
    private String name;

    public JavassistParameterDeclaration(CtClass type, TypeSolver typeSolver, boolean variadic, String name) {
        this(JavassistFactory.typeUsageFor(type, typeSolver), typeSolver, variadic, name);
    }

    public JavassistParameterDeclaration(ResolvedType type, TypeSolver typeSolver, boolean variadic, String name) {
        this.name = name;
        this.type = type;
        this.typeSolver = typeSolver;
        this.variadic = variadic;
    }

    @Override
    public String toString() {
        return "JavassistParameterDeclaration{" +
                "type=" + type +
                ", typeSolver=" + typeSolver +
                ", variadic=" + variadic +
                '}';
    }

    @Override
    public boolean hasName() {
        return name != null;
    }

    @Override
    public String getName() {
        return name;
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
        return type;
    }
}
