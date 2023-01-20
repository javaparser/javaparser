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

package com.github.javaparser.symbolsolver.resolution.typeinference;

import com.github.javaparser.resolution.TypeSolver;

import java.util.LinkedList;
import java.util.List;

/**
 * @author Federico Tomassetti
 */
public class ConstraintFormulaSet {
    private List<ConstraintFormula> constraintFormulas;

    public ConstraintFormulaSet withConstraint(ConstraintFormula constraintFormula) {
        ConstraintFormulaSet newInstance = new ConstraintFormulaSet();
        newInstance.constraintFormulas.addAll(this.constraintFormulas);
        newInstance.constraintFormulas.add(constraintFormula);
        return newInstance;
    }

    private static final ConstraintFormulaSet EMPTY = new ConstraintFormulaSet();

    public static ConstraintFormulaSet empty() {
        return EMPTY;
    }

    private ConstraintFormulaSet() {
        constraintFormulas = new LinkedList<>();
    }

    /**
     * Takes a compatibility assertion about an expression or type, called a constraint formula, and reduces it to a
     * set of bounds on inference variables. Often, a constraint formula reduces to other constraint formulas,
     * which must be recursively reduced. A procedure is followed to identify these additional constraint formulas and,
     * ultimately, to express via a bound set the conditions under which the choices for inferred types would render
     * each constraint formula true.
     */
    public BoundSet reduce(TypeSolver typeSolver) {
        List<ConstraintFormula> constraints = new LinkedList<>(constraintFormulas);
        BoundSet boundSet = BoundSet.empty();
        while (constraints.size() > 0) {
            ConstraintFormula constraintFormula = constraints.remove(0);
            ConstraintFormula.ReductionResult reductionResult = constraintFormula.reduce(boundSet);
            constraints.addAll(reductionResult.getConstraintFormulas());
            boundSet.incorporate(reductionResult.getBoundSet(), typeSolver);
        }
        return boundSet;
    }

    public boolean isEmpty() {
        return constraintFormulas.isEmpty();
    }
}
