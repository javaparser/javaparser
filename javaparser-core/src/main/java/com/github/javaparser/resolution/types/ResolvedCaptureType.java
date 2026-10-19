/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2026 The JavaParser Team.
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

import com.github.javaparser.resolution.Context;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicLong;
import java.util.stream.Collectors;

/**
 * The fresh type variable produced by capture conversion of a lower-bounded wildcard.
 * Its readable members come from the type parameter's upper bounds, while its lower bound
 * determines which values can be written through it (JLS 5.1.10).
 */
public final class ResolvedCaptureType extends ResolvedTypeVariable {

    private static final AtomicLong NEXT_ID = new AtomicLong();

    private final ResolvedWildcard wildcard;

    public ResolvedCaptureType(ResolvedWildcard wildcard, List<ResolvedType> upperBounds) {
        super(ResolvedTypeParameterDeclaration.onType(
                "capture#" + NEXT_ID.incrementAndGet(),
                "capture",
                upperBounds.stream()
                        .map(ResolvedTypeParameterDeclaration.Bound::extendsBound)
                        .collect(Collectors.toList())));
        if (!wildcard.isSuper() || upperBounds.isEmpty()) {
            throw new IllegalArgumentException("A super capture requires a lower bound and at least one upper bound");
        }
        this.wildcard = wildcard;
    }

    /**
     * Whether a type contains a fixed capture, including inside arrays or parameterized types.
     */
    public static boolean containsCapture(ResolvedType type) {
        if (type instanceof ResolvedCaptureType) {
            return true;
        }
        if (type.isArray()) {
            return containsCapture(type.asArrayType().getComponentType());
        }
        if (type.isWildcard()) {
            return type.asWildcard().isBounded()
                    && containsCapture(type.asWildcard().getBoundedType());
        }
        return type.isReferenceType()
                && type.asReferenceType().typeParametersValues().stream()
                        .anyMatch(ResolvedCaptureType::containsCapture);
    }

    public ResolvedWildcard getWildcard() {
        return wildcard;
    }

    @Override
    public String describe() {
        return "capture of " + wildcard.describe();
    }

    @Override
    public boolean isAssignableBy(ResolvedType other) {
        return other == this || other.isNull() || wildcard.getBoundedType().isAssignableBy(other);
    }

    @Override
    public ResolvedType replaceTypeVariables(
            ResolvedTypeParameterDeclaration parameter,
            ResolvedType replacement,
            Map<ResolvedTypeParameterDeclaration, ResolvedType> inferredTypes) {
        return this;
    }

    @Override
    public ResolvedType solveGenericTypes(Context context) {
        return this;
    }

    @Override
    public ResolvedType erasure() {
        return asTypeParameter().getBounds().get(0).getType().erasure();
    }

    @Override
    public String toDescriptor() {
        return erasure().toDescriptor();
    }

    @Override
    public boolean equals(Object other) {
        return this == other;
    }

    @Override
    public int hashCode() {
        return System.identityHashCode(this);
    }
}
