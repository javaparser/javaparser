/*
 * Licensed to the Apache Software Foundation (ASF) under one or more
 * contributor license agreements.  See the NOTICE file distributed with
 * this work for additional information regarding copyright ownership.
 * The ASF licenses this file to You under the Apache License, Version 2.0
 * (the "License"); you may not use this file except in compliance with
 * the License.  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package org.apache.commons.math3.analysis.solvers;

import org.apache.commons.math3.analysis.DifferentiableUnivariateFunction;
import org.apache.commons.math3.analysis.UnivariateFunction;
import org.apache.commons.math3.exception.TooManyEvaluationsException;

/**
 * Provide a default implementation for several functions useful to generic
 * solvers.
 *
 * @since 3.0
 * @deprecated as of 3.1, replaced by {@link AbstractUnivariateDifferentiableSolver}
 */
@Deprecated
public abstract class AbstractDifferentiableUnivariateSolver
    extends BaseAbstractUnivariateSolver<DifferentiableUnivariateFunction>
    implements DifferentiableUnivariateSolver {
    /** Derivative of the function to solve. */
    private UnivariateFunction functionDerivative;

    /**
     * Construct a solver with given absolute accuracy.
     *
     * @param absoluteAccuracy Maximum absolute error.
     */
    protected AbstractDifferentiableUnivariateSolver(final double absoluteAccuracy) {
        super(absoluteAccuracy);
    }

    /**
     * Construct a solver with given accuracies.
     *
     * @param relativeAccuracy Maximum relative error.
     * @param absoluteAccuracy Maximum absolute error.
     * @param functionValueAccuracy Maximum function value error.
     */
    protected AbstractDifferentiableUnivariateSolver(final double relativeAccuracy,
                                                     final double absoluteAccuracy,
                                                     final double functionValueAccuracy) {
        super(relativeAccuracy, absoluteAccuracy, functionValueAccuracy);
    }

    /**
     * Compute the objective function value.
     *
     * @param point Point at which the objective function must be evaluated.
     * @return the objective function value at specified point.
     * @throws TooManyEvaluationsException if the maximal number of evaluations is exceeded.
     */
    protected double computeDerivativeObjectiveValue(double point)
        throws TooManyEvaluationsException {
        incrementEvaluationCount();
        return functionDerivative.value(point);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected void setup(int maxEval, DifferentiableUnivariateFunction f,
                         double min, double max, double startValue) {
        super.setup(maxEval, f, min, max, startValue);
        functionDerivative = f.derivative();
    }
}
