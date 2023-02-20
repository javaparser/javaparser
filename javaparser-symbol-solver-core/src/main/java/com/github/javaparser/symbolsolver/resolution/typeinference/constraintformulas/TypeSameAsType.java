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

    public static boolean[] reduceBranchesReached = new boolean[19];

    public TypeSameAsType(ResolvedType s, ResolvedType t) {
        S = s;
        T = t;
    }

    public static void printReachedBranches(){
        for (int i = 1; i < 19; i++)
            System.out.println("Reduce Branch " + i + (reduceBranchesReached[i] ? "Reached" : "not Reached"));
    }

    @Override
    public ReductionResult reduce(BoundSet currentBoundSet) {
        // A constraint formula of the form ‹S = T›, where S and T are types, is reduced as follows:
        //id 1
        reduceBranchesReached[1] = !S.isWildcard() || reduceBranchesReached[1];
        if (!S.isWildcard() && !T.isWildcard()) {
            //id 2
            reduceBranchesReached[2] = true;
            // - If S and T are proper types, the constraint reduces to true if S is the same as T (§4.3.4), and false
            //   otherwise.
            //id 3
            reduceBranchesReached[3] = isProperType(S) || reduceBranchesReached[3];
            if (isProperType(S) && isProperType(T)) {
                //id 4
                reduceBranchesReached[4] = true;
                if (S.equals(T)) {
                    //id 5
                    reduceBranchesReached[5] = true;
                    return ReductionResult.trueResult();
                } else {
                    //id 6
                    reduceBranchesReached[6] = true;
                    return ReductionResult.falseResult();
                }
            }

            // - Otherwise, if S or T is the null type, the constraint reduces to false.
            //id 7
            reduceBranchesReached[7] = S.isNull();
            if (S.isNull() || T.isNull()) {
                //id 8
                reduceBranchesReached[8] = true;
                return ReductionResult.falseResult();
            }

            // - Otherwise, if S is an inference variable, α, and T is not a primitive type, the constraint reduces to the
            //   bound α = T.
            //id 9
            reduceBranchesReached[9] = S.isInferenceVariable() || reduceBranchesReached[9];
            if (S.isInferenceVariable() && !T.isPrimitive()) {
                //id 10
                reduceBranchesReached[10] = true;
                return ReductionResult.oneBound(new SameAsBound(S, T));
            }

            // - Otherwise, if T is an inference variable, α, and S is not a primitive type, the constraint reduces to the
            //   bound S = α.
            //id 11
            reduceBranchesReached[11] = T.isInferenceVariable() || reduceBranchesReached[9];
            if (T.isInferenceVariable() && !S.isPrimitive()) {
                //id 12
                reduceBranchesReached[12] = true;
                return ReductionResult.oneBound(new SameAsBound(S, T));
            }

            // - Otherwise, if S and T are class or interface types with the same erasure, where S has
            //   type arguments B1, ..., Bn and T has type arguments A1, ..., An, the constraint reduces to the following
            //   new constraints: for all i (1 ≤ i ≤ n), ‹Bi = Ai›.
            //id 13, 14
            reduceBranchesReached[13] = S.isReferenceType() || reduceBranchesReached[13];
            reduceBranchesReached[14] = T.isReferenceType() || reduceBranchesReached[14];
            if (S.isReferenceType() && T.isReferenceType()
                    && S.asReferenceType().toRawType().equals(T.asReferenceType().toRawType())) {
                //id 15
                reduceBranchesReached[15] = true;
                ReductionResult res = ReductionResult.empty();
                List<ResolvedType> Bs = S.asReferenceType().typeParametersValues();
                List<ResolvedType> As = T.asReferenceType().typeParametersValues();
                for (int i = 0; i < Bs.size(); i++) {
                    //id 16
                    reduceBranchesReached[16] = true;
                    res = res.withConstraint(new TypeSameAsType(Bs.get(i), As.get(i)));
                }
                return res;
            }

            // - Otherwise, if S and T are array types, S'[] and T'[], the constraint reduces to ‹S' = T'›.
            //id 17
            reduceBranchesReached[17] = S.isArray() || reduceBranchesReached[17];
            if (S.isArray() && T.isArray()) {
                //id 18
                reduceBranchesReached[18] = true;
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
