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

package com.github.javaparser.symbolsolver.resolution.typeinference;

import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;

import java.util.LinkedList;
import java.util.List;

/**
 * @author Federico Tomassetti
 */
public class Substitution {

    private List<ResolvedTypeParameterDeclaration> typeParameterDeclarations;
    private List<ResolvedType> types;

    private final static Substitution EMPTY = new Substitution();

    public static Substitution empty() {
        return EMPTY;
    }

    public Substitution withPair(ResolvedTypeParameterDeclaration typeParameterDeclaration, ResolvedType type) {
        Substitution newInstance = new Substitution();
        newInstance.typeParameterDeclarations.addAll(this.typeParameterDeclarations);
        newInstance.types.addAll(this.types);
        newInstance.typeParameterDeclarations.add(typeParameterDeclaration);
        newInstance.types.add(type);
        return newInstance;

    }

    private Substitution() {
        this.typeParameterDeclarations = new LinkedList<>();
        this.types = new LinkedList<>();
    }

    public ResolvedType apply(ResolvedType originalType) {
        ResolvedType result = originalType;
        for (int i=0;i<typeParameterDeclarations.size();i++) {
            result = result.replaceTypeVariables(typeParameterDeclarations.get(i), types.get(i));
        }
        return result;
    }
}
