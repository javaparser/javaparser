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

import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.symbolsolver.logic.ObjectProvider;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

/**
 * @author Federico Tomassetti
 */
public class MyObjectProvider implements ObjectProvider {

    public static final MyObjectProvider INSTANCE = new MyObjectProvider();

    private MyObjectProvider() {
        // prevent instantiation
    }

    @Override
    public ResolvedReferenceType object() {
        return new ReferenceTypeImpl(new ReflectionClassDeclaration(Object.class, new ReflectionTypeSolver()), new ReflectionTypeSolver());
    }

    @Override
    public ResolvedReferenceType byName(String qualifiedName) {
        TypeSolver typeSolver = new ReflectionTypeSolver();
        ResolvedReferenceTypeDeclaration typeDeclaration = typeSolver.solveType(qualifiedName);
        if (!typeDeclaration.getTypeParameters().isEmpty()) {
            throw new UnsupportedOperationException();
        }
        return new ReferenceTypeImpl(typeDeclaration, typeSolver);
    }

}
