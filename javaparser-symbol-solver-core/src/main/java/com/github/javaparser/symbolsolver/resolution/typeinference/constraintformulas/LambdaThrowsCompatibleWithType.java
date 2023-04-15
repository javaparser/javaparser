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

import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.resolution.typeinference.BoundSet;
import com.github.javaparser.symbolsolver.resolution.typeinference.ConstraintFormula;

/**
 * The checked exceptions thrown by the body of the LambdaExpression are declared by the throws clause of the
 * function type derived from T.
 *
 * @author Federico Tomassetti
 */
public class LambdaThrowsCompatibleWithType extends ConstraintFormula {
    private LambdaExpr lambdaExpression;
    private ResolvedType T;

    @Override
    public ReductionResult reduce(BoundSet currentBoundSet) {
        // A constraint formula of the form ‹LambdaExpression →throws T› is reduced as follows:
        //
        // - If T is not a functional interface type (§9.8), the constraint reduces to false.
        //
        // - Otherwise, let the target function type for the lambda expression be determined as specified in §15.27.3. If no valid function type can be found, the constraint reduces to false.
        //
        // - Otherwise, if the lambda expression is implicitly typed, and one or more of the function type's parameter types is not a proper type, the constraint reduces to false.
        //
        //   This condition never arises in practice, due to the substitution applied to the target type in §18.5.2.
        //
        // - Otherwise, if the function type's return type is neither void nor a proper type, the constraint reduces to false.
        //
        //   This condition never arises in practice, due to the substitution applied to the target type in §18.5.2.
        //
        // - Otherwise, let E1, ..., En be the types in the function type's throws clause that are not proper types. If the lambda expression is implicitly typed, let its parameter types be the function type's parameter types. If the lambda body is a poly expression or a block containing a poly result expression, let the targeted return type be the function type's return type. Let X1, ..., Xm be the checked exception types that the lambda body can throw (§11.2). Then there are two cases:
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

        LambdaThrowsCompatibleWithType that = (LambdaThrowsCompatibleWithType) o;

        if (!lambdaExpression.equals(that.lambdaExpression)) return false;
        return T.equals(that.T);
    }

    @Override
    public int hashCode() {
        int result = lambdaExpression.hashCode();
        result = 31 * result + T.hashCode();
        return result;
    }

    @Override
    public String toString() {
        return "LambdaThrowsCompatibleWithType{" +
                "lambdaExpression=" + lambdaExpression +
                ", T=" + T +
                '}';
    }
}
