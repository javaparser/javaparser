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

package com.github.javaparser.symbolsolver.resolution.typeinference;

import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

/**
 * Constraint formulas are assertions of compatibility or subtyping that may involve inference variables.
 *
 * @author Federico Tomassetti
 */
public abstract class ConstraintFormula {

    public static class ReductionResult {
        private BoundSet boundSet;
        private List<ConstraintFormula> constraintFormulas;

        public BoundSet getBoundSet() {
            return boundSet;
        }

        public List<ConstraintFormula> getConstraintFormulas() {
            return constraintFormulas;
        }

        public static ReductionResult empty() {
            return new ReductionResult();
        }

        public ReductionResult withConstraint(ConstraintFormula constraintFormula) {
            ReductionResult newInstance = new ReductionResult();
            newInstance.boundSet = this.boundSet;
            newInstance.constraintFormulas = new LinkedList<>();
            newInstance.constraintFormulas.addAll(this.constraintFormulas);
            newInstance.constraintFormulas.add(constraintFormula);
            return newInstance;
        }

        public ReductionResult withBound(Bound bound) {
            ReductionResult newInstance = new ReductionResult();
            newInstance.boundSet = this.boundSet.withBound(bound);
            newInstance.constraintFormulas = this.constraintFormulas;
            return newInstance;
        }

        private ReductionResult() {
            this.boundSet = BoundSet.empty();
            this.constraintFormulas = new LinkedList<>();
        }

        public static ReductionResult trueResult() {
            return empty();
        }

        public static ReductionResult falseResult() {
            return empty().withBound(Bound.falseBound());
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;

            ReductionResult that = (ReductionResult) o;

            if (!boundSet.equals(that.boundSet)) return false;
            return constraintFormulas.equals(that.constraintFormulas);
        }

        @Override
        public int hashCode() {
            int result = boundSet.hashCode();
            result = 31 * result + constraintFormulas.hashCode();
            return result;
        }

        @Override
        public String toString() {
            return "ReductionResult{" +
                    "boundSet=" + boundSet +
                    ", constraintFormulas=" + constraintFormulas +
                    '}';
        }

        public ConstraintFormula getConstraint(int index) {
            if (constraintFormulas.size() <= index) {
                throw new IllegalArgumentException("Constraint with index " + index + " is not available as there are " + constraintFormulas.size() + " constraints");
            }
            return constraintFormulas.get(index);
        }

        public static ReductionResult oneConstraint(ConstraintFormula constraintFormula) {
            return empty().withConstraint(constraintFormula);
        }

        public static ReductionResult withConstraints(ConstraintFormula... constraints) {
            return withConstraints(Arrays.asList(constraints));
        }

        public static ReductionResult oneBound(Bound bound) {
            return empty().withBound(bound);
        }

        public static ReductionResult withConstraints(List<ConstraintFormula> constraints) {
            ReductionResult reductionResult = new ReductionResult();
            reductionResult.constraintFormulas.addAll(constraints);
            return reductionResult;
        }

        public static ReductionResult bounds(BoundSet bounds) {
            ReductionResult reductionResult = new ReductionResult();
            reductionResult.boundSet = bounds;
            return reductionResult;
        }
    }

    /**
     * A formula is reduced to one or both of:
     * i) A bound or bound set, which is to be incorporated with the "current" bound set. Initially, the current bound
     *    set is empty.
     * ii) Further constraint formulas, which are to be reduced recursively.
     */
    public abstract ReductionResult reduce(BoundSet currentBoundSet);

}
