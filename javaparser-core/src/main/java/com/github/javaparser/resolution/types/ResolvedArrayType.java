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

import java.util.Map;

/**
 * Array Type.
 *
 * @author Federico Tomassetti
 */
public class ResolvedArrayType implements ResolvedType {

    private ResolvedType baseType;

    public ResolvedArrayType(ResolvedType baseType) {
        this.baseType = baseType;
    }

    ///
    /// Object methods
    ///

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        ResolvedArrayType that = (ResolvedArrayType) o;

        if (!baseType.equals(that.baseType)) return false;

        return true;
    }

    @Override
    public int hashCode() {
        return baseType.hashCode();
    }

    @Override
    public String toString() {
        return "ResolvedArrayType{" + baseType + "}";
    }

    ///
    /// Type methods
    ///

    @Override
    public ResolvedArrayType asArrayType() {
        return this;
    }

    @Override
    public boolean isArray() {
        return true;
    }

    @Override
    public String describe() {
        return baseType.describe() + "[]";
    }

    public ResolvedType getComponentType() {
        return baseType;
    }

    @Override
    public boolean isAssignableBy(ResolvedType other) {
        if (other.isArray()) {
            if (baseType.isPrimitive() && other.asArrayType().getComponentType().isPrimitive()) {
              return baseType.equals(other.asArrayType().getComponentType());
            }
            return baseType.isAssignableBy(other.asArrayType().getComponentType());
        } else if (other.isNull()) {
            return true;
        }
        return false;
    }

    @Override
    public ResolvedType replaceTypeVariables(ResolvedTypeParameterDeclaration tpToReplace, ResolvedType replaced, Map<ResolvedTypeParameterDeclaration, ResolvedType> inferredTypes) {
        ResolvedType baseTypeReplaced = baseType.replaceTypeVariables(tpToReplace, replaced, inferredTypes);
        if (baseTypeReplaced == baseType) {
            return this;
        } else {
            return new ResolvedArrayType(baseTypeReplaced);
        }
    }

}
