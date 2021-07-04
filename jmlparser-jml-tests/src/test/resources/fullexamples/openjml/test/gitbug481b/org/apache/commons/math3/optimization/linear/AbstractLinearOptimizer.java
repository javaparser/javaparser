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

package org.apache.commons.math3.optimization.linear;

import java.util.Collection;
import java.util.Collections;

import org.apache.commons.math3.exception.MathIllegalStateException;
import org.apache.commons.math3.exception.MaxCountExceededException;
import org.apache.commons.math3.optimization.GoalType;
import org.apache.commons.math3.optimization.PointValuePair;

/**
 * Base class for implementing linear optimizers.
 * <p>
 * This base class handles the boilerplate methods associated to thresholds
 * settings and iterations counters.
 *
 * @deprecated As of 3.1 (to be removed in 4.0).
 * @since 2.0
 */
@Deprecated
public abstract class AbstractLinearOptimizer implements LinearOptimizer {

    /** Default maximal number of iterations allowed. */
    public static final int DEFAULT_MAX_ITERATIONS = 100;

    /**
     * Linear objective function.
     * @since 2.1
     */
    private LinearObjectiveFunction function;

    /**
     * Linear constraints.
     * @since 2.1
     */
    private Collection<LinearConstraint> linearConstraints;

    /**
     * Type of optimization goal: either {@link GoalType#MAXIMIZE} or {@link GoalType#MINIMIZE}.
     * @since 2.1
     */
    private GoalType goal;

    /**
     * Whether to restrict the variables to non-negative values.
     * @since 2.1
     */
    private boolean nonNegative;

    /** Maximal number of iterations allowed. */
    private int maxIterations;

    /** Number of iterations already performed. */
    private int iterations;

    /**
     * Simple constructor with default settings.
     * <p>The maximal number of evaluation is set to its default value.</p>
     */
    protected AbstractLinearOptimizer() {
        setMaxIterations(DEFAULT_MAX_ITERATIONS);
    }

    /**
     * @return {@code true} if the variables are restricted to non-negative values.
     */
    protected boolean restrictToNonNegative() {
        return nonNegative;
    }

    /**
     * @return the optimization type.
     */
    protected GoalType getGoalType() {
        return goal;
    }

    /**
     * @return the optimization type.
     */
    protected LinearObjectiveFunction getFunction() {
        return function;
    }

    /**
     * @return the optimization type.
     */
    protected Collection<LinearConstraint> getConstraints() {
        return Collections.unmodifiableCollection(linearConstraints);
    }

    /** {@inheritDoc} */
    public void setMaxIterations(int maxIterations) {
        this.maxIterations = maxIterations;
    }

    /** {@inheritDoc} */
    public int getMaxIterations() {
        return maxIterations;
    }

    /** {@inheritDoc} */
    public int getIterations() {
        return iterations;
    }

    /**
     * Increment the iterations counter by 1.
     * @exception MaxCountExceededException if the maximal number of iterations is exceeded
     */
    protected void incrementIterationsCounter()
        throws MaxCountExceededException {
        if (++iterations > maxIterations) {
            throw new MaxCountExceededException(maxIterations);
        }
    }

    /** {@inheritDoc} */
    public PointValuePair optimize(final LinearObjectiveFunction f,
                                   final Collection<LinearConstraint> constraints,
                                   final GoalType goalType, final boolean restrictToNonNegative)
        throws MathIllegalStateException {

        // store linear problem characteristics
        this.function          = f;
        this.linearConstraints = constraints;
        this.goal              = goalType;
        this.nonNegative       = restrictToNonNegative;

        iterations  = 0;

        // solve the problem
        return doOptimize();

    }

    /**
     * Perform the bulk of optimization algorithm.
     * @return the point/value pair giving the optimal value for objective function
     * @exception MathIllegalStateException if no solution fulfilling the constraints
     * can be found in the allowed number of iterations
     */
    protected abstract PointValuePair doOptimize() throws MathIllegalStateException;

}
