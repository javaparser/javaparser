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

package org.apache.commons.math3.optimization.univariate;

import org.apache.commons.math3.util.Incrementor;
import org.apache.commons.math3.exception.MaxCountExceededException;
import org.apache.commons.math3.exception.TooManyEvaluationsException;
import org.apache.commons.math3.exception.NullArgumentException;
import org.apache.commons.math3.analysis.UnivariateFunction;
import org.apache.commons.math3.optimization.GoalType;
import org.apache.commons.math3.optimization.ConvergenceChecker;

/**
 * Provide a default implementation for several functions useful to generic
 * optimizers.
 *
 * @deprecated As of 3.1 (to be removed in 4.0).
 * @since 2.0
 */
@Deprecated
public abstract class BaseAbstractUnivariateOptimizer
    implements UnivariateOptimizer {
    /** Convergence checker. */
    private final ConvergenceChecker<UnivariatePointValuePair> checker;
    /** Evaluations counter. */
    private final Incrementor evaluations = new Incrementor();
    /** Optimization type */
    private GoalType goal;
    /** Lower end of search interval. */
    private double searchMin;
    /** Higher end of search interval. */
    private double searchMax;
    /** Initial guess . */
    private double searchStart;
    /** Function to optimize. */
    private UnivariateFunction function;

    /**
     * @param checker Convergence checking procedure.
     */
    protected BaseAbstractUnivariateOptimizer(ConvergenceChecker<UnivariatePointValuePair> checker) {
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

    /**
     * @return the optimization type.
     */
    public GoalType getGoalType() {
        return goal;
    }
    /**
     * @return the lower end of the search interval.
     */
    public double getMin() {
        return searchMin;
    }
    /**
     * @return the higher end of the search interval.
     */
    public double getMax() {
        return searchMax;
    }
    /**
     * @return the initial guess.
     */
    public double getStartValue() {
        return searchStart;
    }

    /**
     * Compute the objective function value.
     *
     * @param point Point at which the objective function must be evaluated.
     * @return the objective function value at specified point.
     * @throws TooManyEvaluationsException if the maximal number of evaluations
     * is exceeded.
     */
    protected double computeObjectiveValue(double point) {
        try {
            evaluations.incrementCount();
        } catch (MaxCountExceededException e) {
            throw new TooManyEvaluationsException(e.getMax());
        }
        return function.value(point);
    }

    /** {@inheritDoc} */
    public UnivariatePointValuePair optimize(int maxEval, UnivariateFunction f,
                                             GoalType goalType,
                                             double min, double max,
                                             double startValue) {
        // Checks.
        if (f == null) {
            throw new NullArgumentException();
        }
        if (goalType == null) {
            throw new NullArgumentException();
        }

        // Reset.
        searchMin = min;
        searchMax = max;
        searchStart = startValue;
        goal = goalType;
        function = f;
        evaluations.setMaximalCount(maxEval);
        evaluations.resetCount();

        // Perform computation.
        return doOptimize();
    }

    /** {@inheritDoc} */
    public UnivariatePointValuePair optimize(int maxEval,
                                             UnivariateFunction f,
                                             GoalType goalType,
                                             double min, double max){
        return optimize(maxEval, f, goalType, min, max, min + 0.5 * (max - min));
    }

    /**
     * {@inheritDoc}
     */
    public ConvergenceChecker<UnivariatePointValuePair> getConvergenceChecker() {
        return checker;
    }

    /**
     * Method for implementing actual optimization algorithms in derived
     * classes.
     *
     * @return the optimum and its corresponding function value.
     * @throws TooManyEvaluationsException if the maximal number of evaluations
     * is exceeded.
     */
    protected abstract UnivariatePointValuePair doOptimize();
}
