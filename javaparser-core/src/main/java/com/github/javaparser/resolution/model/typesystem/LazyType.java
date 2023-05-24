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
package com.github.javaparser.resolution.model.typesystem;

import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.types.*;
import java.util.Map;
import java.util.function.Function;

public class LazyType implements ResolvedType {

    private ResolvedType concrete;

    private Function<Void, ResolvedType> provider;

    public LazyType(Function<Void, ResolvedType> provider) {
        this.provider = provider;
    }

    private ResolvedType getType() {
        if (concrete == null) {
            concrete = provider.apply(null);
        }
        return concrete;
    }

    @Override
    public boolean isArray() {
        return getType().isArray();
    }

    @Override
    public int arrayLevel() {
        return getType().arrayLevel();
    }

    @Override
    public boolean isPrimitive() {
        return getType().isPrimitive();
    }

    @Override
    public boolean isNull() {
        return getType().isNull();
    }

    @Override
    public boolean isReference() {
        return getType().isReference();
    }

    @Override
    public boolean isReferenceType() {
        return getType().isReferenceType();
    }

    @Override
    public boolean isVoid() {
        return getType().isVoid();
    }

    @Override
    public boolean isTypeVariable() {
        return getType().isTypeVariable();
    }

    @Override
    public boolean isWildcard() {
        return getType().isWildcard();
    }

    @Override
    public ResolvedArrayType asArrayType() {
        return getType().asArrayType();
    }

    @Override
    public ResolvedReferenceType asReferenceType() {
        return getType().asReferenceType();
    }

    @Override
    public ResolvedTypeParameterDeclaration asTypeParameter() {
        return getType().asTypeParameter();
    }

    @Override
    public ResolvedTypeVariable asTypeVariable() {
        return getType().asTypeVariable();
    }

    @Override
    public ResolvedPrimitiveType asPrimitive() {
        return getType().asPrimitive();
    }

    @Override
    public ResolvedWildcard asWildcard() {
        return getType().asWildcard();
    }

    @Override
    public String describe() {
        return getType().describe();
    }

    @Override
    public ResolvedType replaceTypeVariables(ResolvedTypeParameterDeclaration tp, ResolvedType replaced, Map<ResolvedTypeParameterDeclaration, ResolvedType> inferredTypes) {
        return getType().replaceTypeVariables(tp, replaced, inferredTypes);
    }

    @Override
    public ResolvedType replaceTypeVariables(ResolvedTypeParameterDeclaration tp, ResolvedType replaced) {
        return getType().replaceTypeVariables(tp, replaced);
    }

    @Override
    public boolean isAssignableBy(ResolvedType other) {
        return getType().isAssignableBy(other);
    }
}
