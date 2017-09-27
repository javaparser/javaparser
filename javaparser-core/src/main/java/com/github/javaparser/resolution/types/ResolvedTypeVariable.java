/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2016 The JavaParser Team.
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

package com.github.javaparser.resolution.types;

import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;

import java.util.List;
import java.util.Map;

/**
 * From JLS 4.4: A type variable is introduced by the declaration of a type parameter of a generic class,
 * interface, method, or constructor (§8.1.2, §9.1.2, §8.4.4, §8.8.4).
 *
 * @author Federico Tomassetti
 */
public class ResolvedTypeVariable implements ResolvedType {

    private ResolvedTypeParameterDeclaration typeParameter;

    public ResolvedTypeVariable(ResolvedTypeParameterDeclaration typeParameter) {
        this.typeParameter = typeParameter;
    }

    @Override
    public String toString() {
        return "TypeVariable {" + typeParameter.getQualifiedName() + "}";
    }

    public String qualifiedName() {
        return this.typeParameter.getQualifiedName();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        ResolvedTypeVariable that = (ResolvedTypeVariable) o;

        if (!typeParameter.getName().equals(that.typeParameter.getName())) return false;
        if (typeParameter.declaredOnType() != that.typeParameter.declaredOnType()) return false;
        if (typeParameter.declaredOnMethod() != that.typeParameter.declaredOnMethod()) return false;

        return true;
    }

    @Override
    public int hashCode() {
        return typeParameter.hashCode();
    }

    @Override
    public boolean isArray() {
        return false;
    }

    @Override
    public boolean isPrimitive() {
        return false;
    }

    @Override
    public ResolvedType replaceTypeVariables(ResolvedTypeParameterDeclaration tpToBeReplaced, ResolvedType replaced, Map<ResolvedTypeParameterDeclaration, ResolvedType> inferredTypes) {
        if(tpToBeReplaced.getName().equals(this.typeParameter.getName())){
            inferredTypes.put(this.asTypeParameter(), replaced);
            return replaced;
        } else {
            return this;
        }
    }

    @Override
    public boolean isReferenceType() {
        return false;
    }

    @Override
    public String describe() {
        return typeParameter.getName();
    }

    @Override
    public ResolvedTypeParameterDeclaration asTypeParameter() {
        return typeParameter;
    }

    @Override
    public ResolvedTypeVariable asTypeVariable() {
        return this;
    }

    @Override
    public boolean isTypeVariable() {
        return true;
    }

    @Override
    public boolean isAssignableBy(ResolvedType other) {
        if (other.isTypeVariable()) {
            return describe().equals(other.describe());
        } else {
            return true;
        }
    }

    @Override
    public boolean mention(List<ResolvedTypeParameterDeclaration> typeParameters) {
        return typeParameters.contains(typeParameter);
    }
}
