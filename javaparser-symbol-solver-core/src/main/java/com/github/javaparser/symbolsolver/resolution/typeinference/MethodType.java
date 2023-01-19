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

package com.github.javaparser.symbolsolver.resolution.typeinference;

import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;

import java.util.List;

/**
 * A MethodType is an ordered 4-tuple consisting of:
 * 1. type parameters: the declarations of any type parameters of the method member.
 * 2. argument types: a list of the types of the arguments to the method member.
 * 3. return type: the return type of the method member.
 * 4. throws clause: exception types declared in the throws clause of the method member.
 *
 * See JLS 8.2
 *
 * @author Federico Tomassetti
 */
public class MethodType {
    private List<ResolvedTypeParameterDeclaration> typeParameters;
    private List<ResolvedType> formalArgumentTypes;
    private ResolvedType returnType;
    private List<ResolvedType> exceptionTypes;

    public static MethodType fromMethodUsage(MethodUsage methodUsage) {
        return new MethodType(methodUsage.getDeclaration().getTypeParameters(), methodUsage.getParamTypes(),
                methodUsage.returnType(), methodUsage.exceptionTypes());
    }

    public MethodType(List<ResolvedTypeParameterDeclaration> typeParameters, List<ResolvedType> formalArgumentTypes,
                      ResolvedType returnType,
                      List<ResolvedType> exceptionTypes) {
        this.typeParameters = typeParameters;
        this.formalArgumentTypes = formalArgumentTypes;
        this.returnType = returnType;
        this.exceptionTypes = exceptionTypes;
    }

    public List<ResolvedTypeParameterDeclaration> getTypeParameters() {
        return typeParameters;
    }

    public List<ResolvedType> getFormalArgumentTypes() {
        return formalArgumentTypes;
    }

    public ResolvedType getReturnType() {
        return returnType;
    }

    public List<ResolvedType> getExceptionTypes() {
        return exceptionTypes;
    }
}
