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

import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * A resolved type. It could be a primitive type or a reference type (enum, class, interface). In the later case it
 * could take type typeParametersValues (other TypeUsages). It could also be a TypeVariable, like in:
 * <p>
 * class A&lt;Bgt; { }
 * <p>
 * where B is a TypeVariable. It could also be Wildcard Type, possibly with constraints.
 *
 * @author Federico Tomassetti
 */
public interface ResolvedType {

    ///
    /// Relation with other types
    ///

    /**
     * Does this type represent an array?
     */
    default boolean isArray() {
        return false;
    }

    default int arrayLevel() {
        if (isArray()) {
            return 1 + this.asArrayType().getComponentType().arrayLevel();
        } else {
            return 0;
        }
    }

    /**
     * Is this a primitive type?
     */
    default boolean isPrimitive() {
        return false;
    }

    /**
     * Is this the null type?
     */
    default boolean isNull() {
        return false;
    }

    /**
     * Is this a union type (as the ones used in multi catch clauses)?
     */
    default boolean isUnionType() {
        return false;
    }

    /**
     * Is this a non primitive value?
     */
    default boolean isReference() {
        return isReferenceType() || isArray() || isTypeVariable() || isNull() || isWildcard() || isUnionType();
    }

    /**
     * Is this a lambda constraint type?
     */
    default boolean isConstraint() { return false; }

    /**
     * Can this be seen as a ReferenceTypeUsage?
     * In other words: is this a reference to a class, an interface or an enum?
     */
    default boolean isReferenceType() {
        return false;
    }

    default boolean isVoid() {
        return false;
    }

    default boolean isTypeVariable() {
        return false;
    }

    default boolean isWildcard() {
        return false;
    }

    ///
    /// Downcasting
    ///

    default ResolvedArrayType asArrayType() {
        throw new UnsupportedOperationException(String.format("%s is not an Array", this));
    }

    default ResolvedReferenceType asReferenceType() {
        throw new UnsupportedOperationException(String.format("%s is not a Reference Type", this));
    }

    default ResolvedTypeParameterDeclaration asTypeParameter() {
        throw new UnsupportedOperationException(String.format("%s is not a Type parameter", this));
    }

    default ResolvedTypeVariable asTypeVariable() {
        throw new UnsupportedOperationException(String.format("%s is not a Type variable", this));
    }

    default ResolvedPrimitiveType asPrimitive() {
        throw new UnsupportedOperationException(String.format("%s is not a Primitive type", this));
    }

    default ResolvedWildcard asWildcard() {
        throw new UnsupportedOperationException(String.format("%s is not a Wildcard", this));
    }

    default ResolvedLambdaConstraintType asConstraintType() {
        throw new UnsupportedOperationException(String.format("%s is not a constraint type", this));
    }

    default ResolvedUnionType asUnionType() {
        throw new UnsupportedOperationException(String.format("%s is not a union type", this));
    }

    ///
    /// Naming
    ///

    String describe();

    ///
    /// TypeParameters
    ///

    /**
     * Replace all variables referring to the given TypeParameter with the given value.
     * By replacing these values I could also infer some type equivalence.
     * Those would be collected in the given map.
     */
    default ResolvedType replaceTypeVariables(ResolvedTypeParameterDeclaration tp, ResolvedType replaced, Map<ResolvedTypeParameterDeclaration, ResolvedType> inferredTypes) {
        return this;
    }

    /**
     * This is like ({@link #replaceTypeVariables(ResolvedTypeParameterDeclaration, ResolvedType, Map)} but ignores the inferred values.
     */
    default ResolvedType replaceTypeVariables(ResolvedTypeParameterDeclaration tp, ResolvedType replaced) {
        return replaceTypeVariables(tp, replaced, new HashMap<>());
    }

    /**
     * Does this type mention at all, directly or indirectly, the given type parameters?
     */
    default boolean mention(List<ResolvedTypeParameterDeclaration> typeParameters) {
        throw new UnsupportedOperationException(this.getClass().getCanonicalName());
    }

    ///
    /// Assignability
    ///

    /**
     * This method checks if ThisType t = new OtherType() would compile.
     */
    boolean isAssignableBy(ResolvedType other);

}
