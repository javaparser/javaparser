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

import org.apache.commons.math3.util.Incrementor;
import org.apache.commons.math3.exception.MaxCountExceededException;
import org.apache.commons.math3.exception.TooManyEvaluationsException;
import org.apache.commons.math3.analysis.MultivariateFunction;
import org.apache.commons.math3.optimization.BaseMultivariateOptimizer;
import org.apache.commons.math3.optimization.OptimizationData;
import org.apache.commons.math3.optimization.GoalType;
import org.apache.commons.math3.optimization.InitialGuess;
import org.apache.commons.math3.optimization.SimpleBounds;
import org.apache.commons.math3.optimization.ConvergenceChecker;
import org.apache.commons.math3.optimization.PointValuePair;
import org.apache.commons.math3.optimization.SimpleValueChecker;
import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.NumberIsTooSmallException;
import org.apache.commons.math3.exception.NumberIsTooLargeException;

/**
 * Base class for implementing optimizers for multivariate scalar functions.
 * This base class handles the boiler-plate methods associated to thresholds,
 * evaluations counting, initial guess and simple bounds settings.
 *
 * @param <FUNC> Type of the objective function to be optimized.
 *
 * @deprecated As of 3.1 (to be removed in 4.0).
 * @since 2.2
 */
@Deprecated
public abstract class BaseAbstractMultivariateOptimizer<FUNC extends MultivariateFunction>
    implements BaseMultivariateOptimizer<FUNC> {
    /** Evaluations counter. */
    protected final Incrementor evaluations = new Incrementor();
    /** Convergence checker. */
    private ConvergenceChecker<PointValuePair> checker;
    /** Type of optimization. */
    private GoalType goal;
    /** Initial guess. */
    private double[] start;
    /** Lower bounds. */
    private double[] lowerBound;
    /** Upper bounds. */
    private double[] upperBound;
    /** Objective function. */
    private MultivariateFunction function;

    /**
     * Simple constructor with default settings.
     * The convergence check is set to a {@link SimpleValueChecker}.
     * @deprecated See {@link SimpleValueChecker#SimpleValueChecker()}
     */
    @Deprecated
    protected BaseAbstractMultivariateOptimizer() {
        this(new SimpleValueChecker());
    }
    /**
     * @param checker Convergence checker.
     */
    protected BaseAbstractMultivariateOptimizer(ConvergenceChecker<PointValuePair> checker) {
        this.checker = checker;
    }

    /** {@inheritDoc} */
    public int getMaxEvaluations() {
        return evaluations.getMaximalCount();
    }

    /** {@inheritDoc} */
    public int getEvaluations() {
        return evaluations.getCount();
    }

    /** {@inheritDoc} */
    public ConvergenceChecker<PointValuePair> getConvergenceChecker() {
        return checker;
    }

    /**
     * Compute the objective function value.
     *
     * @param point Point at which the objective function must be evaluated.
     * @return the objective function value at the specified point.
     * @throws TooManyEvaluationsException if the maximal number of
     * evaluations is exceeded.
     */
    protected double computeObjectiveValue(double[] point) {
        try {
            evaluations.incrementCount();
        } catch (MaxCountExceededException e) {
            throw new TooManyEvaluationsException(e.getMax());
        }
        return function.value(point);
    }

    /**
     * {@inheritDoc}
     *
     * @deprecated As of 3.1. Please use
     * {@link #optimize(int,MultivariateFunction,GoalType,OptimizationData[])}
     * instead.
     */
    @Deprecated
    public PointValuePair optimize(int maxEval, FUNC f, GoalType goalType,
                                   double[] startPoint) {
        return optimizeInternal(maxEval, f, goalType, new InitialGuess(startPoint));
    }

    /**
     * Optimize an objective function.
     *
     * @param maxEval Allowed number of evaluations of the objective function.
     * @param f Objective function.
     * @param goalType Optimization type.
     * @param optData Optimization data. The following data will be looked for:
     * <ul>
     *  <li>{@link InitialGuess}</li>
     *  <li>{@link SimpleBounds}</li>
     * </ul>
     * @return the point/value pair giving the optimal value of the objective
     * function.
     * @since 3.1
     */
    public PointValuePair optimize(int maxEval,
                                   FUNC f,
                                   GoalType goalType,
                                   OptimizationData... optData) {
        return optimizeInternal(maxEval, f, goalType, optData);
    }

    /**
     * Optimize an objective function.
     *
     * @param f Objective function.
     * @param goalType Type of optimization goal: either
     * {@link GoalType#MAXIMIZE} or {@link GoalType#MINIMIZE}.
     * @param startPoint Start point for optimization.
     * @param maxEval Maximum number of function evaluations.
     * @return the point/value pair giving the optimal value for objective
     * function.
     * @throws org.apache.commons.math3.exception.DimensionMismatchException
     * if the start point dimension is wrong.
     * @throws org.apache.commons.math3.exception.TooManyEvaluationsException
     * if the maximal number of evaluations is exceeded.
     * @throws org.apache.commons.math3.exception.NullArgumentException if
     * any argument is {@code null}.
     * @deprecated As of 3.1. Please use
     * {@link #optimize(int,MultivariateFunction,GoalType,OptimizationData[])}
     * instead.
     */
    @Deprecated
    protected PointValuePair optimizeInternal(int maxEval, FUNC f, GoalType goalType,
                                              double[] startPoint) {
        return optimizeInternal(maxEval, f, goalType, new InitialGuess(startPoint));
    }

    /**
     * Optimize an objective function.
     *
     * @param maxEval Allowed number of evaluations of the objective function.
     * @param f Objective function.
     * @param goalType Optimization type.
     * @param optData Optimization data. The following data will be looked for:
     * <ul>
     *  <li>{@link InitialGuess}</li>
     *  <li>{@link SimpleBounds}</li>
     * </ul>
     * @return the point/value pair giving the optimal value of the objective
     * function.
     * @throws TooManyEvaluationsException if the maximal number of
     * evaluations is exceeded.
     * @since 3.1
     */
    protected PointValuePair optimizeInternal(int maxEval,
                                              FUNC f,
                                              GoalType goalType,
                                              OptimizationData... optData)
        throws TooManyEvaluationsException {
        // Set internal state.
        evaluations.setMaximalCount(maxEval);
        evaluations.resetCount();
        function = f;
        goal = goalType;
        // Retrieve other settings.
        parseOptimizationData(optData);
        // Check input consistency.
        checkParameters();
        // Perform computation.
        return doOptimize();
    }

    /**
     * Scans the list of (required and optional) optimization data that
     * characterize the problem.
     *
     * @param optData Optimization data. The following data will be looked for:
     * <ul>
     *  <li>{@link InitialGuess}</li>
     *  <li>{@link SimpleBounds}</li>
     * </ul>
     */
    private void parseOptimizationData(OptimizationData... optData) {
        // The existing values (as set by the previous call) are reused if
        // not provided in the argument list.
        for (OptimizationData data : optData) {
            if (data instanceof InitialGuess) {
                start = ((InitialGuess) data).getInitialGuess();
                continue;
            }
            if (data instanceof SimpleBounds) {
                final SimpleBounds bounds = (SimpleBounds) data;
                lowerBound = bounds.getLower();
                upperBound = bounds.getUpper();
                continue;
            }
        }
    }

    /**
     * @return the optimization type.
     */
    public GoalType getGoalType() {
        return goal;
    }

    /**
     * @return the initial guess.
     */
    public double[] getStartPoint() {
        return start == null ? null : start.clone();
    }
    /**
     * @return the lower bounds.
     * @since 3.1
     */
    public double[] getLowerBound() {
        return lowerBound == null ? null : lowerBound.clone();
    }
    /**
     * @return the upper bounds.
     * @since 3.1
     */
    public double[] getUpperBound() {
        return upperBound == null ? null : upperBound.clone();
    }

    /**
     * Perform the bulk of the optimization algorithm.
     *
     * @return the point/value pair giving the optimal value of the
     * objective function.
     */
    protected abstract PointValuePair doOptimize();

    /**
     * Check parameters consistency.
     */
    private void checkParameters() {
        if (start != null) {
            final int dim = start.length;
            if (lowerBound != null) {
                if (lowerBound.length != dim) {
                    throw new DimensionMismatchException(lowerBound.length, dim);
                }
                for (int i = 0; i < dim; i++) {
                    final double v = start[i];
                    final double lo = lowerBound[i];
                    if (v < lo) {
                        throw new NumberIsTooSmallException(v, lo, true);
                    }
                }
            }
            if (upperBound != null) {
                if (upperBound.length != dim) {
                    throw new DimensionMismatchException(upperBound.length, dim);
                }
                for (int i = 0; i < dim; i++) {
                    final double v = start[i];
                    final double hi = upperBound[i];
                    if (v > hi) {
                        throw new NumberIsTooLargeException(v, hi, true);
                    }
                }
            }

            // If the bounds were not specified, the allowed interval is
            // assumed to be [-inf, +inf].
            if (lowerBound == null) {
                lowerBound = new double[dim];
                for (int i = 0; i < dim; i++) {
                    lowerBound[i] = Double.NEGATIVE_INFINITY;
                }
            }
            if (upperBound == null) {
                upperBound = new double[dim];
                for (int i = 0; i < dim; i++) {
                    upperBound[i] = Double.POSITIVE_INFINITY;
                }
            }
        }
    }
}
