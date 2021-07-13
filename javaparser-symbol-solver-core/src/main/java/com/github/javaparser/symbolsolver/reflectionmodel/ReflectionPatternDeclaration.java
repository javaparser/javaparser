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

import com.github.javaparser.resolution.declarations.ResolvedPatternDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;

/**
 * WARNING: Implemented fairly blindly. Unsure if required or even appropriate. Use with extreme caution.
 *
 * @author Roger Howell
 */
public class ReflectionPatternDeclaration implements ResolvedPatternDeclaration {

    private Class<?> type;
    private TypeSolver typeSolver;
    private String name;

    /**
     * @param type
     * @param typeSolver
     * @param name       can potentially be null
     */
    public ReflectionPatternDeclaration(Class<?> type, TypeSolver typeSolver, String name) {
        this.type = type;
        this.typeSolver = typeSolver;
        this.name = name;
    }

    @Override
    public String getName() {
        return name;
    }

    @Override
    public boolean hasName() {
        return name != null;
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
    public boolean isPattern() {
        return true;
    }

    @Override
    public boolean isType() {
        return false;
    }

    @Override
    public ResolvedType getType() {
        return ReflectionFactory.typeUsageFor(type, typeSolver);
    }

}
