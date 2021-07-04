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
package org.apache.commons.math3.optim.univariate;

import org.apache.commons.math3.analysis.UnivariateFunction;
import org.apache.commons.math3.optim.BaseOptimizer;
import org.apache.commons.math3.optim.OptimizationData;
import org.apache.commons.math3.optim.nonlinear.scalar.GoalType;
import org.apache.commons.math3.optim.ConvergenceChecker;
import org.apache.commons.math3.exception.TooManyEvaluationsException;

/**
 * Base class for a univariate scalar function optimizer.
 *
 * @since 3.1
 */
public abstract class UnivariateOptimizer
    extends BaseOptimizer<UnivariatePointValuePair> {
    /** Objective function. */
    private UnivariateFunction function;
    /** Type of optimization. */
    private GoalType goal;
    /** Initial guess. */
    private double start;
    /** Lower bound. */
    private double min;
    /** Upper bound. */
    private double max;

    /**
     * @param checker Convergence checker.
     */
    protected UnivariateOptimizer(ConvergenceChecker<UnivariatePointValuePair> checker) {
        super(checker);
    }

    /**
     * {@inheritDoc}
     *
     * @param optData Optimization data. In addition to those documented in
     * {@link BaseOptimizer#parseOptimizationData(OptimizationData[])
     * BaseOptimizer}, this method will register the following data:
     * <ul>
     *  <li>{@link GoalType}</li>
     *  <li>{@link SearchInterval}</li>
     *  <li>{@link UnivariateObjectiveFunction}</li>
     * </ul>
     * @return {@inheritDoc}
     * @throws TooManyEvaluationsException if the maximal number of
     * evaluations is exceeded.
     */
    @Override
    public UnivariatePointValuePair optimize(OptimizationData... optData)
        throws TooManyEvaluationsException {
        // Perform computation.
        return super.optimize(optData);
    }

    /**
     * @return the optimization type.
     */
    public GoalType getGoalType() {
        return goal;
    }

    /**
     * Scans the list of (required and optional) optimization data that
     * characterize the problem.
     *
     * @param optData Optimization data.
     * The following data will be looked for:
     * <ul>
     *  <li>{@link GoalType}</li>
     *  <li>{@link SearchInterval}</li>
     *  <li>{@link UnivariateObjectiveFunction}</li>
     * </ul>
     */
    @Override
    protected void parseOptimizationData(OptimizationData... optData) {
        // Allow base class to register its own data.
        super.parseOptimizationData(optData);

        // The existing values (as set by the previous call) are reused if
        // not provided in the argument list.
        for (OptimizationData data : optData) {
            if (data instanceof SearchInterval) {
                final SearchInterval interval = (SearchInterval) data;
                min = interval.getMin();
                max = interval.getMax();
                start = interval.getStartValue();
                continue;
            }
            if (data instanceof UnivariateObjectiveFunction) {
                function = ((UnivariateObjectiveFunction) data).getObjectiveFunction();
                continue;
            }
            if (data instanceof GoalType) {
                goal = (GoalType) data;
                continue;
            }
        }
    }

    /**
     * @return the initial guess.
     */
    public double getStartValue() {
        return start;
    }
    /**
     * @return the lower bounds.
     */
    public double getMin() {
        return min;
    }
    /**
     * @return the upper bounds.
     */
    public double getMax() {
        return max;
    }

    /**
     * Computes the objective function value.
     * This method <em>must</em> be called by subclasses to enforce the
     * evaluation counter limit.
     *
     * @param x Point at which the objective function must be evaluated.
     * @return the objective function value at the specified point.
     * @throws TooManyEvaluationsException if the maximal number of
     * evaluations is exceeded.
     */
    protected double computeObjectiveValue(double x) {
        super.incrementEvaluationCount();
        return function.value(x);
    }
}
