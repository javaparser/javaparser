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

import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.model.typesystem.NullType;
import com.github.javaparser.resolution.types.ResolvedIntersectionType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.resolution.typeinference.BoundSet;
import com.github.javaparser.symbolsolver.resolution.typeinference.ConstraintFormula;
import com.github.javaparser.symbolsolver.resolution.typeinference.bounds.SubtypeOfBound;

import static com.github.javaparser.symbolsolver.resolution.typeinference.TypeHelper.isProperType;

/**
 * A reference type S is a subtype of a reference type T
 *
 * @author Federico Tomassetti
 */
public class TypeSubtypeOfType extends ConstraintFormula {
    private ResolvedType S;
    private ResolvedType T;
    private TypeSolver typeSolver;

    public TypeSubtypeOfType(TypeSolver typeSolver, ResolvedType S, ResolvedType T) {
        this.typeSolver = typeSolver;
        this.S = S;
        this.T = T;
    }

    @Override
    public ReductionResult reduce(BoundSet currentBoundSet) {
        // A constraint formula of the form ‹S <: T› is reduced as follows:
        //
        // - If S and T are proper types, the constraint reduces to true if S is a subtype of T (§4.10), and false otherwise.

        if (isProperType(S) && isProperType(T)) {
            if (T.isAssignableBy(S)) {
                return ReductionResult.trueResult();
            }
            return ReductionResult.falseResult();
        }

        // - Otherwise, if S is the null type, the constraint reduces to true.

        if (S instanceof NullType) {
            return ReductionResult.trueResult();
        }

        // - Otherwise, if T is the null type, the constraint reduces to false.

        if (T instanceof NullType) {
            return ReductionResult.falseResult();
        }

        // - Otherwise, if S is an inference variable, α, the constraint reduces to the bound α <: T.

        if (S.isInferenceVariable()) {
            return ReductionResult.oneBound(new SubtypeOfBound(S, T));
        }

        // - Otherwise, if T is an inference variable, α, the constraint reduces to the bound S <: α.

        if (T.isInferenceVariable()) {
            return ReductionResult.oneBound(new SubtypeOfBound(S, T));
        }

        // FEDERICO - Added start
        //if (T.isTypeVariable()) {
        //    return ReductionResult.oneBound(new SubtypeOfBound(S, T));
        //}
        // FEDERICO - Added end

        // - Otherwise, the constraint is reduced according to the form of T:
        //
        //   - If T is a parameterized class or interface type, or an inner class type of a parameterized class or interface type (directly or indirectly), let A1, ..., An be the type arguments of T. Among the supertypes of S, a corresponding class or interface type is identified, with type arguments B1, ..., Bn. If no such type exists, the constraint reduces to false. Otherwise, the constraint reduces to the following new constraints: for all i (1 ≤ i ≤ n), ‹Bi <= Ai›.
        //
        //   - If T is any other class or interface type, then the constraint reduces to true if T is among the supertypes of S, and false otherwise.
        //
        //   - If T is an array type, T'[], then among the supertypes of S that are array types, a most specific type is identified, S'[] (this may be S itself). If no such array type exists, the constraint reduces to false. Otherwise:
        //
        //     - If neither S' nor T' is a primitive type, the constraint reduces to ‹S' <: T'›.
        //
        //     - Otherwise, the constraint reduces to true if S' and T' are the same primitive type, and false otherwise.
        //
        //   - If T is a type variable, there are three cases:

        if (T.isTypeVariable()) {

            //     - If S is an intersection type of which T is an element, the constraint reduces to true.

            if (S instanceof ResolvedIntersectionType) {
                throw new UnsupportedOperationException();
            }

            //     - Otherwise, if T has a lower bound, B, the constraint reduces to ‹S <: B›.

            if (T.asTypeVariable().asTypeParameter().hasLowerBound()) {
                return ReductionResult.oneConstraint(new TypeSubtypeOfType(typeSolver, S, T.asTypeVariable().asTypeParameter().getLowerBound()));
            }

            //     - Otherwise, the constraint reduces to false.

            return ReductionResult.falseResult();
        }

        //
        //   - If T is an intersection type, I1 & ... & In, the constraint reduces to the following new constraints: for all i (1 ≤ i ≤ n), ‹S <: Ii›.
        //

        throw new UnsupportedOperationException("S = "+ S + ", T = " + T);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        TypeSubtypeOfType that = (TypeSubtypeOfType) o;

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
        return "TypeSubtypeOfType{" +
                "S=" + S +
                ", T=" + T +
                '}';
    }
}
