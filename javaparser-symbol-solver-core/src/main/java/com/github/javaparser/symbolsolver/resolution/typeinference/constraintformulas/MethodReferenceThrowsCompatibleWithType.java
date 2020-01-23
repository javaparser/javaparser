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

import com.github.javaparser.ast.expr.MethodReferenceExpr;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.resolution.typeinference.BoundSet;
import com.github.javaparser.symbolsolver.resolution.typeinference.ConstraintFormula;

/**
 * The checked exceptions thrown by the referenced method are declared by the throws clause of the function type
 * derived from T.
 *
 * @author Federico Tomassetti
 */
public class MethodReferenceThrowsCompatibleWithType extends ConstraintFormula {
    private MethodReferenceExpr methodReference;
    private ResolvedType T;

    @Override
    public ReductionResult reduce(BoundSet currentBoundSet) {
        // A constraint formula of the form ‹MethodReference →throws T› is reduced as follows:
        //
        // - If T is not a functional interface type, or if T is a functional interface type but does not have a function type (§9.9), the constraint reduces to false.
        //
        // - Otherwise, let the target function type for the method reference expression be the function type of T. If the method reference is inexact (§15.13.1) and one or more of the function type's parameter types is not a proper type, the constraint reduces to false.
        //
        // - Otherwise, if the method reference is inexact and the function type's result is neither void nor a proper type, the constraint reduces to false.
        //
        // - Otherwise, let E1, ..., En be the types in the function type's throws clause that are not proper types. Let X1, ..., Xm be the checked exceptions in the throws clause of the invocation type of the method reference's compile-time declaration (§15.13.2) (as derived from the function type's parameter types and return type). Then there are two cases:
        //
        //   - If n = 0 (the function type's throws clause consists only of proper types), then if there exists some i (1 ≤ i ≤ m) such that Xi is not a subtype of any proper type in the throws clause, the constraint reduces to false; otherwise, the constraint reduces to true.
        //
        //   - If n > 0, the constraint reduces to a set of subtyping constraints: for all i (1 ≤ i ≤ m), if Xi is not a subtype of any proper type in the throws clause, then the constraints include, for all j (1 ≤ j ≤ n), ‹Xi <: Ej›. In addition, for all j (1 ≤ j ≤ n), the constraint reduces to the bound throws Ej.

        throw new UnsupportedOperationException();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        MethodReferenceThrowsCompatibleWithType that = (MethodReferenceThrowsCompatibleWithType) o;

        if (!methodReference.equals(that.methodReference)) return false;
        return T.equals(that.T);
    }

    @Override
    public int hashCode() {
        int result = methodReference.hashCode();
        result = 31 * result + T.hashCode();
        return result;
    }

    @Override
    public String toString() {
        return "MethodReferenceThrowsCompatibleWithType{" +
                "methodReference=" + methodReference +
                ", T=" + T +
                '}';
    }
}
