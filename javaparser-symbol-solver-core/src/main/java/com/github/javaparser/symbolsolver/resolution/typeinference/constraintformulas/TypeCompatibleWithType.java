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
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.symbolsolver.resolution.typeinference.BoundSet;
import com.github.javaparser.symbolsolver.resolution.typeinference.ConstraintFormula;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

import static com.github.javaparser.symbolsolver.resolution.typeinference.TypeHelper.isCompatibleInALooseInvocationContext;
import static com.github.javaparser.symbolsolver.resolution.typeinference.TypeHelper.isProperType;

/**
 * A type S is compatible in a loose invocation context with type T
 *
 * @author Federico Tomassetti
 */
public class TypeCompatibleWithType extends ConstraintFormula {
    private ResolvedType s;
    private ResolvedType t;
    private TypeSolver typeSolver;

    public TypeCompatibleWithType(TypeSolver typeSolver, ResolvedType s, ResolvedType t) {
        this.typeSolver = typeSolver;
        this.s = s;
        this.t = t;
    }

    @Override
    public ReductionResult reduce(BoundSet currentBoundSet) {
        // A constraint formula of the form ‹S → T› is reduced as follows:
        //
        // 1. If S and T are proper types, the constraint reduces to true if S is compatible in a loose invocation context with T (§5.3), and false otherwise.

        if (isProperType(s) && isProperType(t)) {
            if (isCompatibleInALooseInvocationContext(s, t)) {
                return ReductionResult.trueResult();
            } else {
                return ReductionResult.falseResult();
            }
        }

        // 2. Otherwise, if S is a primitive type, let S' be the result of applying boxing conversion (§5.1.7) to S. Then the constraint reduces to ‹S' → T›.

        if (s.isPrimitive()) {
            ReflectionTypeSolver typeSolver = new ReflectionTypeSolver();
            ResolvedType sFirst = new ReferenceTypeImpl(typeSolver.solveType(s.asPrimitive().getBoxTypeQName()), typeSolver);
            return ReductionResult.oneConstraint(new TypeCompatibleWithType(typeSolver, sFirst, t));
        }

        // 3. Otherwise, if T is a primitive type, let T' be the result of applying boxing conversion (§5.1.7) to T. Then the constraint reduces to ‹S = T'›.

        if (t.isPrimitive()) {
            ReflectionTypeSolver typeSolver = new ReflectionTypeSolver();
            ResolvedType tFirst = new ReferenceTypeImpl(typeSolver.solveType(t.asPrimitive().getBoxTypeQName()), typeSolver);
            return ReductionResult.oneConstraint(new TypeSameAsType(s, tFirst));
        }

        // The fourth and fifth cases are implicit uses of unchecked conversion (§5.1.9). These, along with any use of
        // unchecked conversion in the first case, may result in compile-time unchecked warnings, and may influence a
        // method's invocation type (§15.12.2.6).

        // 4. Otherwise, if T is a parameterized type of the form G<T1, ..., Tn>, and there exists no type of the
        //    form G<...> that is a supertype of S, but the raw type G is a supertype of S, then the constraint reduces
        //    to true.

        if (t.isReferenceType() && t.asReferenceType().getTypeDeclaration().isPresent() && !t.asReferenceType().getTypeDeclaration().get().getTypeParameters().isEmpty()) {
            // FIXME I really cannot understand what the specification means...

            // there exists a type of the form G<...> that is a supertype of S?
            boolean condition1 = t.isAssignableBy(s);

            // the raw type G is a supertype of S
            ResolvedType G = t.asReferenceType().toRawType();
            boolean condition2 = G.isAssignableBy(s);

            if (!condition1 && condition2) {
                return ReductionResult.trueResult();
            }

            //throw new UnsupportedOperationException();
        }

        // 5. Otherwise, if T is an array type of the form G<T1, ..., Tn>[]k, and there exists no type of the form
        //    G<...>[]k that is a supertype of S, but the raw type G[]k is a supertype of S, then the constraint
        //    reduces to true. (The notation []k indicates an array type of k dimensions.)

        if (t.isArray()) {
            throw new UnsupportedOperationException();
        }

        // 6. Otherwise, the constraint reduces to ‹S <: T›

        return ReductionResult.empty().withConstraint(new TypeSubtypeOfType(typeSolver, s, t));
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        TypeCompatibleWithType that = (TypeCompatibleWithType) o;

        if (!s.equals(that.s)) return false;
        return t.equals(that.t);
    }

    @Override
    public int hashCode() {
        int result = s.hashCode();
        result = 31 * result + t.hashCode();
        return result;
    }

    @Override
    public String toString() {
        return "TypeCompatibleWithType{" +
                "s=" + s +
                ", t=" + t +
                '}';
    }
}
