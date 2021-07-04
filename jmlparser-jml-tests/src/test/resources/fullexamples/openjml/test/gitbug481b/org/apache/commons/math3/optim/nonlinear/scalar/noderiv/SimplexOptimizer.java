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
package org.apache.commons.math3.optim.nonlinear.scalar.noderiv;

import java.util.Comparator;
import org.apache.commons.math3.analysis.MultivariateFunction;
import org.apache.commons.math3.exception.NullArgumentException;
import org.apache.commons.math3.exception.MathUnsupportedOperationException;
import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.optim.nonlinear.scalar.GoalType;
import org.apache.commons.math3.optim.ConvergenceChecker;
import org.apache.commons.math3.optim.PointValuePair;
import org.apache.commons.math3.optim.SimpleValueChecker;
import org.apache.commons.math3.optim.OptimizationData;
import org.apache.commons.math3.optim.nonlinear.scalar.MultivariateOptimizer;

/**
 * This class implements simplex-based direct search optimization.
 *
 * <p>
 *  Direct search methods only use objective function values, they do
 *  not need derivatives and don't either try to compute approximation
 *  of the derivatives. According to a 1996 paper by Margaret H. Wright
 *  (<a href="http://cm.bell-labs.com/cm/cs/doc/96/4-02.ps.gz">Direct
 *  Search Methods: Once Scorned, Now Respectable</a>), they are used
 *  when either the computation of the derivative is impossible (noisy
 *  functions, unpredictable discontinuities) or difficult (complexity,
 *  computation cost). In the first cases, rather than an optimum, a
 *  <em>not too bad</em> point is desired. In the latter cases, an
 *  optimum is desired but cannot be reasonably found. In all cases
 *  direct search methods can be useful.
 * </p>
 * <p>
 *  Simplex-based direct search methods are based on comparison of
 *  the objective function values at the vertices of a simplex (which is a
 *  set of n+1 points in dimension n) that is updated by the algorithms
 *  steps.
 * <p>
 * <p>
 *  The simplex update procedure ({@link NelderMeadSimplex} or
 * {@link MultiDirectionalSimplex})  must be passed to the
 * {@code optimize} method.
 * </p>
 * <p>
 *  Each call to {@code optimize} will re-use the start configuration of
 *  the current simplex and move it such that its first vertex is at the
 *  provided start point of the optimization.
 *  If the {@code optimize} method is called to solve a different problem
 *  and the number of parameters change, the simplex must be re-initialized
 *  to one with the appropriate dimensions.
 * </p>
 * <p>
 *  Convergence is checked by providing the <em>worst</em> points of
 *  previous and current simplex to the convergence checker, not the best
 *  ones.
 * </p>
 * <p>
 *  This simplex optimizer implementation does not directly support constrained
 *  optimization with simple bounds; so, for such optimizations, either a more
 *  dedicated algorithm must be used like
 *  {@link CMAESOptimizer} or {@link BOBYQAOptimizer}, or the objective
 *  function must be wrapped in an adapter like
 *  {@link org.apache.commons.math3.optim.nonlinear.scalar.MultivariateFunctionMappingAdapter
 *  MultivariateFunctionMappingAdapter} or
 *  {@link org.apache.commons.math3.optim.nonlinear.scalar.MultivariateFunctionPenaltyAdapter
 *  MultivariateFunctionPenaltyAdapter}.
 *  <br/>
 *  The call to {@link #optimize(OptimizationData[]) optimize} will throw
 *  {@link MathUnsupportedOperationException} if bounds are passed to it.
 * </p>
 *
 * @since 3.0
 */
public class SimplexOptimizer extends MultivariateOptimizer {
    /** Simplex update rule. */
    private AbstractSimplex simplex;

    /**
     * @param checker Convergence checker.
     */
    public SimplexOptimizer(ConvergenceChecker<PointValuePair> checker) {
        super(checker);
    }

    /**
     * @param rel Relative threshold.
     * @param abs Absolute threshold.
     */
    public SimplexOptimizer(double rel, double abs) {
        this(new SimpleValueChecker(rel, abs));
    }

    /**
     * {@inheritDoc}
     *
     * @param optData Optimization data. In addition to those documented in
     * {@link MultivariateOptimizer#parseOptimizationData(OptimizationData[])
     * MultivariateOptimizer}, this method will register the following data:
     * <ul>
     *  <li>{@link AbstractSimplex}</li>
     * </ul>
     * @return {@inheritDoc}
     */
    @Override
    public PointValuePair optimize(OptimizationData... optData) {
        // Set up base class and perform computation.
        return super.optimize(optData);
    }

    /** {@inheritDoc} */
    @Override
    protected PointValuePair doOptimize() {
        checkParameters();

        // Indirect call to "computeObjectiveValue" in order to update the
        // evaluations counter.
        final MultivariateFunction evalFunc
            = new MultivariateFunction() {
                /** {@inheritDoc} */
                public double value(double[] point) {
                    return computeObjectiveValue(point);
                }
            };

        final boolean isMinim = getGoalType() == GoalType.MINIMIZE;
        final Comparator<PointValuePair> comparator
            = new Comparator<PointValuePair>() {
            /** {@inheritDoc} */
            public int compare(final PointValuePair o1,
                               final PointValuePair o2) {
                final double v1 = o1.getValue();
                final double v2 = o2.getValue();
                return isMinim ? Double.compare(v1, v2) : Double.compare(v2, v1);
            }
        };

        // Initialize search.
        simplex.build(getStartPoint());
        simplex.evaluate(evalFunc, comparator);

        PointValuePair[] previous = null;
        int iteration = 0;
        final ConvergenceChecker<PointValuePair> checker = getConvergenceChecker();
        while (true) {
            if (getIterations() > 0) {
                boolean converged = true;
                for (int i = 0; i < simplex.getSize(); i++) {
                    PointValuePair prev = previous[i];
                    converged = converged &&
                        checker.converged(iteration, prev, simplex.getPoint(i));
                }
                if (converged) {
                    // We have found an optimum.
                    return simplex.getPoint(0);
                }
            }

            // We still need to search.
            previous = simplex.getPoints();
            simplex.iterate(evalFunc, comparator);

            incrementIterationCount();
        }
    }

    /**
     * Scans the list of (required and optional) optimization data that
     * characterize the problem.
     *
     * @param optData Optimization data.
     * The following data will be looked for:
     * <ul>
     *  <li>{@link AbstractSimplex}</li>
     * </ul>
     */
    @Override
    protected void parseOptimizationData(OptimizationData... optData) {
        // Allow base class to register its own data.
        super.parseOptimizationData(optData);

        // The existing values (as set by the previous call) are reused if
        // not provided in the argument list.
        for (OptimizationData data : optData) {
            if (data instanceof AbstractSimplex) {
                simplex = (AbstractSimplex) data;
                // If more data must be parsed, this statement _must_ be
                // changed to "continue".
                break;
            }
        }
    }

    /**
     * @throws MathUnsupportedOperationException if bounds were passed to the
     * {@link #optimize(OptimizationData[]) optimize} method.
     * @throws NullArgumentException if no initial simplex was passed to the
     * {@link #optimize(OptimizationData[]) optimize} method.
     */
    private void checkParameters() {
        if (simplex == null) {
            throw new NullArgumentException();
        }
        if (getLowerBound() != null ||
            getUpperBound() != null) {
            throw new MathUnsupportedOperationException(LocalizedFormats.CONSTRAINT);
        }
    }
}
