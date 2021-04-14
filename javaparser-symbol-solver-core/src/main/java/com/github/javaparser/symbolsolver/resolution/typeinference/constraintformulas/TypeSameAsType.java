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

package com.github.javaparser.symbolsolver.resolution.typeinference.constraintformulas;

import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.resolution.typeinference.BoundSet;
import com.github.javaparser.symbolsolver.resolution.typeinference.ConstraintFormula;
import com.github.javaparser.symbolsolver.resolution.typeinference.bounds.SameAsBound;

import java.util.List;

import static com.github.javaparser.symbolsolver.resolution.typeinference.TypeHelper.isProperType;

/**
 * A type S is the same as a type T (§4.3.4), or a type argument S is the same as type argument T
 *
 * @author Federico Tomassetti
 */
public class TypeSameAsType extends ConstraintFormula {
    private ResolvedType S;
    private ResolvedType T;

    public TypeSameAsType(ResolvedType s, ResolvedType t) {
        S = s;
        T = t;
    }

    @Override
    public ReductionResult reduce(BoundSet currentBoundSet) {
        // A constraint formula of the form ‹S = T›, where S and T are types, is reduced as follows:

        if (!S.isWildcard() && !T.isWildcard()) {

            // - If S and T are proper types, the constraint reduces to true if S is the same as T (§4.3.4), and false
            //   otherwise.

            if (isProperType(S) && isProperType(T)) {
                if (S.equals(T)) {
                    return ReductionResult.trueResult();
                } else {
                    return ReductionResult.falseResult();
                }
            }

            // - Otherwise, if S or T is the null type, the constraint reduces to false.

            if (S.isNull() || T.isNull()) {
                return ReductionResult.falseResult();
            }

            // - Otherwise, if S is an inference variable, α, and T is not a primitive type, the constraint reduces to the
            //   bound α = T.

            if (S.isInferenceVariable() && !T.isPrimitive()) {
                return ReductionResult.oneBound(new SameAsBound(S, T));
            }

            // - Otherwise, if T is an inference variable, α, and S is not a primitive type, the constraint reduces to the
            //   bound S = α.

            if (T.isInferenceVariable() && !S.isPrimitive()) {
                return ReductionResult.oneBound(new SameAsBound(S, T));
            }

            // - Otherwise, if S and T are class or interface types with the same erasure, where S has
            //   type arguments B1, ..., Bn and T has type arguments A1, ..., An, the constraint reduces to the following
            //   new constraints: for all i (1 ≤ i ≤ n), ‹Bi = Ai›.

            if (S.isReferenceType() && T.isReferenceType()
                    && S.asReferenceType().toRawType().equals(T.asReferenceType().toRawType())) {
                ReductionResult res = ReductionResult.empty();
                List<ResolvedType> Bs = S.asReferenceType().typeParametersValues();
                List<ResolvedType> As = T.asReferenceType().typeParametersValues();
                for (int i = 0; i < Bs.size(); i++) {
                    res = res.withConstraint(new TypeSameAsType(Bs.get(i), As.get(i)));
                }
                return res;
            }

            // - Otherwise, if S and T are array types, S'[] and T'[], the constraint reduces to ‹S' = T'›.

            if (S.isArray() && T.isArray()) {
                return ReductionResult.oneConstraint(new TypeSameAsType(
                        S.asArrayType().getComponentType(),
                        T.asArrayType().getComponentType()));
            }

            // - Otherwise, the constraint reduces to false.

            return ReductionResult.falseResult();
        }

        // Note that we do not address intersection types above, because it is impossible for reduction to encounter an
        // intersection type that is not a proper type.

        // A constraint formula of the form ‹S = T›, where S and T are type arguments (§4.5.1), is reduced as follows:
        //
        // - If S and T are types, the constraint is reduced as described above.
        //
        // - If S has the form ? and T has the form ?, the constraint reduces to true.
        //
        // - If S has the form ? and T has the form ? extends T', the constraint reduces to ‹Object = T'›.
        //
        // - If S has the form ? extends S' and T has the form ?, the constraint reduces to ‹S' = Object›.
        //
        // - If S has the form ? extends S' and T has the form ? extends T', the constraint reduces to ‹S' = T'›.
        //
        // - If S has the form ? super S' and T has the form ? super T', the constraint reduces to ‹S' = T'›.
        //
        // - Otherwise, the constraint reduces to false.


        throw new UnsupportedOperationException();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        TypeSameAsType that = (TypeSameAsType) o;

        if (!S.equals(that.S)) return false;
        return T.equals(that.T);
    }

    @Override
    public int hashCode() {
        int result = S.hashCode();
        result = 31 * result + T.hashCode();
        return result;
    }

    @Override
    public String toString() {
        return "TypeSameAsType{" +
                "S=" + S +
                ", T=" + T +
                '}';
    }
}
