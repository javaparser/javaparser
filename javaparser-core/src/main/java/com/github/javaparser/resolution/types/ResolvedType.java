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

import com.github.javaparser.resolution.Context;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * <p>A resolved type. </p>
 * <ul>
 *     <li>
 *         It could be a primitive type or a reference type (enum, class, interface).
 *         In the latter case, it could take type typeParametersValues (other {@code TypeUsages}).</p>
 *     </li>
 *     <li>
 *         It could also be a {@code TypeVariable}, like in: {@code class A<B> {} } where {@code B} is a {@code TypeVariable}.
 *     </li>
 *     <li>
 *         It could also be {@code Wildcard} Type, possibly with constraints.
 *     </li>
 *     <li>
 *         It could also be a {@code TypeVariable}, like in: {@code class A<B> {}}.
 *     </li>
 * </ul>
 *
 * @author Federico Tomassetti
 */
public interface ResolvedType {

    // /
    // / Relation with other types
    // /
    /**
     * @return true, if this type represent an array - otherwise false.
     */
    default boolean isArray() {
        return false;
    }

    /**
     * @return The level of nesting that this type is present at.
     * For example, int[][] would have an array level of 2, and int would have an array level of 0 (not an array).
     */
    default int arrayLevel() {
        if (isArray()) {
            return 1 + this.asArrayType().getComponentType().arrayLevel();
        }
        return 0;
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
    default boolean isConstraint() {
        return false;
    }

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

    default boolean isInferenceVariable() {
        return false;
    }

    // /
    // / Downcasting
    // /
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

    // /
    // / Naming
    // /
    String describe();

    // /
    // / TypeParameters
    // /
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

    // /
    // / Assignability
    // /
    /**
     * This method checks if ThisType t = new OtherType() would compile.
     */
    boolean isAssignableBy(ResolvedType other);

    /*
     * Returns true if the ResolvedType is a numeric
     */
    default boolean isNumericType() {
        return Arrays.stream(ResolvedPrimitiveType.getNumericPrimitiveTypes()).anyMatch(rpt -> rpt.isAssignableBy(this));
    }

    // /
    // / Erasure
    // /
    // Type erasure is a mapping from types (possibly including parameterized types and type variables) to types (that
    // / are never parameterized types or type variables). We write |T| for the erasure of type T. The erasure mapping
    // / is defined as follows:
    //
    // The erasure of a parameterized type (§4.5) G<T1,...,Tn> is |G|.
    //
    // The erasure of a nested type T.C is |T|.C.
    //
    // The erasure of an array type T[] is |T|[].
    //
    // The erasure of a type variable (§4.4) is the erasure of its leftmost bound.
    //
    // The erasure of every other type is the type itself.
    default ResolvedType erasure() {
        return this;
    }

    /*
     * Returns the resolved type for a type variable or the bounded resolved type or the type itself.
     */
    default ResolvedType solveGenericTypes(Context context) {
        return this;
    }

    default String toDescriptor() {
        return "";
    }
}
