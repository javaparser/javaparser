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
 * A wildcard can be:
 * - unbounded (?)
 * - have a lower bound (? super Number)
 * - have an upper bound (? extends Number)
 * It is not possible to have both a lower and an upper bound at the same time.
 *
 * @author Federico Tomassetti
 */
public class ResolvedWildcard implements ResolvedType {

    public static ResolvedWildcard UNBOUNDED = new ResolvedWildcard(null, null);

    private BoundType type;
    private ResolvedType boundedType;

    private ResolvedWildcard(BoundType type, ResolvedType boundedType) {
        if (type == null && boundedType != null) {
            throw new IllegalArgumentException();
        }
        if (type != null && boundedType == null) {
            throw new IllegalArgumentException();
        }
        this.type = type;
        this.boundedType = boundedType;
    }

    public static ResolvedWildcard superBound(ResolvedType type) {
        return new ResolvedWildcard(BoundType.SUPER, type);
    }

    public static ResolvedWildcard extendsBound(ResolvedType type) {
        return new ResolvedWildcard(BoundType.EXTENDS, type);
    }

    @Override
    public String toString() {
        return "WildcardUsage{" +
                "type=" + type +
                ", boundedType=" + boundedType +
                '}';
    }

    public boolean isWildcard() {
        return true;
    }

    public ResolvedWildcard asWildcard() {
        return this;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof ResolvedWildcard)) return false;

        ResolvedWildcard that = (ResolvedWildcard) o;

        if (boundedType != null ? !boundedType.equals(that.boundedType) : that.boundedType != null) return false;
        if (type != that.type) return false;

        return true;
    }

    @Override
    public int hashCode() {
        int result = type != null ? type.hashCode() : 0;
        result = 31 * result + (boundedType != null ? boundedType.hashCode() : 0);
        return result;
    }

    @Override
    public String describe() {
        if (type == null) {
            return "?";
        } else if (type == BoundType.SUPER) {
            return "? super " + boundedType.describe();
        } else if (type == BoundType.EXTENDS) {
            return "? extends " + boundedType.describe();
        } else {
            throw new UnsupportedOperationException();
        }
    }

    public boolean isSuper() {
        return type == BoundType.SUPER;
    }

    public boolean isExtends() {
        return type == BoundType.EXTENDS;
    }

    public boolean isBounded() {
        return isSuper() || isExtends();
    }

    public ResolvedType getBoundedType() {
        if (boundedType == null) {
            throw new IllegalStateException();
        }
        return boundedType;
    }

    @Override
    public boolean isAssignableBy(ResolvedType other) {
        if (boundedType == null) {
            //return other.isReferenceType() && other.asReferenceType().getQualifiedName().equals(Object.class.getCanonicalName());
            return false;
        } else if (type == BoundType.SUPER) {
            return boundedType.isAssignableBy(other);
        } else if (type == BoundType.EXTENDS) {
            return false;
        } else {
            throw new RuntimeException();
        }
    }

    @Override
    public ResolvedType replaceTypeVariables(ResolvedTypeParameterDeclaration tpToReplace, ResolvedType replaced, Map<ResolvedTypeParameterDeclaration, ResolvedType> inferredTypes) {
        if (replaced == null) {
            throw new IllegalArgumentException();
        }
        if (boundedType == null) {
            return this;
        }
        ResolvedType boundedTypeReplaced = boundedType.replaceTypeVariables(tpToReplace, replaced, inferredTypes);
        if (boundedTypeReplaced == null) {
            throw new RuntimeException();
        }
        if (boundedTypeReplaced != boundedType) {
            return new ResolvedWildcard(type, boundedTypeReplaced);
        } else {
            return this;
        }
    }

    @Override
    public boolean mention(List<ResolvedTypeParameterDeclaration> typeParameters) {
        return boundedType != null && boundedType.mention(typeParameters);
    }

    public boolean isUpperBounded() {
        return isSuper();
    }

    public boolean isLowerBounded() {
        return isExtends();
    }

    public enum BoundType {
        SUPER,
        EXTENDS
    }

}
