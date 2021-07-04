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

package org.apache.commons.math3.optimization.direct;

import java.util.Comparator;

import org.apache.commons.math3.analysis.MultivariateFunction;
import org.apache.commons.math3.exception.NullArgumentException;
import org.apache.commons.math3.optimization.GoalType;
import org.apache.commons.math3.optimization.ConvergenceChecker;
import org.apache.commons.math3.optimization.PointValuePair;
import org.apache.commons.math3.optimization.SimpleValueChecker;
import org.apache.commons.math3.optimization.MultivariateOptimizer;
import org.apache.commons.math3.optimization.OptimizationData;

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
 *  The {@link #setSimplex(AbstractSimplex) setSimplex} method <em>must</em>
 *  be called prior to calling the {@code optimize} method.
 * </p>
 * <p>
 *  Each call to {@link #optimize(int,MultivariateFunction,GoalType,double[])
 *  optimize} will re-use the start configuration of the current simplex and
 *  move it such that its first vertex is at the provided start point of the
 *  optimization. If the {@code optimize} method is called to solve a different
 *  problem and the number of parameters change, the simplex must be
 *  re-initialized to one with the appropriate dimensions.
 * </p>
 * <p>
 *  Convergence is checked by providing the <em>worst</em> points of
 *  previous and current simplex to the convergence checker, not the best
 *  ones.
 * </p>
 * <p>
 * This simplex optimizer implementation does not directly support constrained
 * optimization with simple bounds, so for such optimizations, either a more
 * dedicated method must be used like {@link CMAESOptimizer} or {@link
 * BOBYQAOptimizer}, or the optimized method must be wrapped in an adapter like
 * {@link MultivariateFunctionMappingAdapter} or {@link
 * MultivariateFunctionPenaltyAdapter}.
 * </p>
 *
 * @see AbstractSimplex
 * @see MultivariateFunctionMappingAdapter
 * @see MultivariateFunctionPenaltyAdapter
 * @see CMAESOptimizer
 * @see BOBYQAOptimizer
 * @deprecated As of 3.1 (to be removed in 4.0).
 * @since 3.0
 */
@SuppressWarnings("boxing") // deprecated anyway
@Deprecated
public class SimplexOptimizer
    extends BaseAbstractMultivariateOptimizer<MultivariateFunction>
    implements MultivariateOptimizer {
    /** Simplex. */
    private AbstractSimplex simplex;

    /**
     * Constructor using a default {@link SimpleValueChecker convergence
     * checker}.
     * @deprecated See {@link SimpleValueChecker#SimpleValueChecker()}
     */
    @Deprecated
    public SimplexOptimizer() {
        this(new SimpleValueChecker());
    }

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
     * Set the simplex algorithm.
     *
     * @param simplex Simplex.
     * @deprecated As of 3.1. The initial simplex can now be passed as an
     * argument of the {@link #optimize(int,MultivariateFunction,GoalType,OptimizationData[])}
     * method.
     */
    @Deprecated
    public void setSimplex(AbstractSimplex simplex) {
        parseOptimizationData(simplex);
    }

    /**
     * Optimize an objective function.
     *
     * @param maxEval Allowed number of evaluations of the objective function.
     * @param f Objective function.
     * @param goalType Optimization type.
     * @param optData Optimization data. The following data will be looked for:
     * <ul>
     *  <li>{@link org.apache.commons.math3.optimization.InitialGuess InitialGuess}</li>
     *  <li>{@link AbstractSimplex}</li>
     * </ul>
     * @return the point/value pair giving the optimal value for objective
     * function.
     */
    @Override
    protected PointValuePair optimizeInternal(int maxEval, MultivariateFunction f,
                                              GoalType goalType,
                                              OptimizationData... optData) {
        // Scan "optData" for the input specific to this optimizer.
        parseOptimizationData(optData);

        // The parent's method will retrieve the common parameters from
        // "optData" and call "doOptimize".
        return super.optimizeInternal(maxEval, f, goalType, optData);
    }

    /**
     * Scans the list of (required and optional) optimization data that
     * characterize the problem.
     *
     * @param optData Optimization data. The following data will be looked for:
     * <ul>
     *  <li>{@link AbstractSimplex}</li>
     * </ul>
     */
    private void parseOptimizationData(OptimizationData... optData) {
        // The existing values (as set by the previous call) are reused if
        // not provided in the argument list.
        for (OptimizationData data : optData) {
            if (data instanceof AbstractSimplex) {
                simplex = (AbstractSimplex) data;
                continue;
            }
        }
    }

    /** {@inheritDoc} */
    @Override
    protected PointValuePair doOptimize() {
        if (simplex == null) {
            throw new NullArgumentException();
        }

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
            if (iteration > 0) {
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
            ++iteration;
        }
    }
}
