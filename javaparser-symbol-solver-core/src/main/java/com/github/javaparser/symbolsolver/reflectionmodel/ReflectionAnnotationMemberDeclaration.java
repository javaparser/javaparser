/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2019 The JavaParser Team.
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

import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.resolution.declarations.ResolvedAnnotationMemberDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;

import java.lang.reflect.Method;

/**
 * @author Malte Skoruppa
 */
public class ReflectionAnnotationMemberDeclaration implements ResolvedAnnotationMemberDeclaration {

    private Method annotationMember;
    private TypeSolver typeSolver;

    public ReflectionAnnotationMemberDeclaration(Method annotationMember, TypeSolver typeSolver) {
        this.annotationMember = annotationMember;
        this.typeSolver = typeSolver;
    }

    @Override
    public Expression getDefaultValue() {
        // TODO we should do this:
        // return annotationMember.getDefaultValue();
        // TODO ...but the interface wants us to return a JavaParser Expression node.
        throw new UnsupportedOperationException("Obtaining the default value of a reflection annotation member is not supported yet.");
    }

    @Override
    public ResolvedType getType() {
        throw new UnsupportedOperationException();
    }

    @Override
    public String getName() {
        return annotationMember.getName();
    }
}
