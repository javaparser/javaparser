/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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

import java.util.Map;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;

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

    // /
    // / Object methods
    // /
    @Override
    public boolean equals(Object o) {
        if (this == o)
            return true;
        if (o == null || getClass() != o.getClass())
            return false;
        ResolvedArrayType that = (ResolvedArrayType) o;
        if (!baseType.equals(that.baseType))
            return false;
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

    // /
    // / Type methods
    // /
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
    public // https://docs.oracle.com/javase/specs/jls/se8/html/jls-5.html#jls-5.2
    boolean isAssignableBy(ResolvedType other) {
        if (other.isNull()) {
            return true;
        }
        if (other.isArray()) {
            if (baseType.isPrimitive() && other.asArrayType().getComponentType().isPrimitive()) {
                return baseType.equals(other.asArrayType().getComponentType());
            }
            // An array of primitive type is not assignable by an array of boxed type nor the reverse
            // An array of primitive type cannot be assigned to an array of Object
            if ((baseType.isPrimitive() && other.asArrayType().getComponentType().isReferenceType()) || (baseType.isReferenceType() && other.asArrayType().getComponentType().isPrimitive())) {
                return false;
            }
            // An array can be assigned only to a variable of a compatible array type, or to
            // a variable of type Object, Cloneable or java.io.Serializable.
            return baseType.isAssignableBy(other.asArrayType().getComponentType());
        }
        return false;
    }

    @Override
    public ResolvedType replaceTypeVariables(ResolvedTypeParameterDeclaration tpToReplace, ResolvedType replaced, Map<ResolvedTypeParameterDeclaration, ResolvedType> inferredTypes) {
        ResolvedType baseTypeReplaced = baseType.replaceTypeVariables(tpToReplace, replaced, inferredTypes);
        if (baseTypeReplaced == baseType) {
            return this;
        }
        return new ResolvedArrayType(baseTypeReplaced);
    }

    // /
    // / Erasure
    // /
    // The erasure of an array type T[] is |T|[].
    @Override
    public ResolvedType erasure() {
        return new ResolvedArrayType(baseType.erasure());
    }

    @Override
    public String toDescriptor() {
        StringBuffer sb = new StringBuffer();
        sb.append("[");
        sb.append(baseType.toDescriptor());
        return sb.toString();
    }
}
