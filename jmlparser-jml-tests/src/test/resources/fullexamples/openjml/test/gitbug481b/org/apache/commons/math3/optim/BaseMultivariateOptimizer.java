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
package org.apache.commons.math3.optim;

import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.NumberIsTooSmallException;
import org.apache.commons.math3.exception.NumberIsTooLargeException;

/**
 * Base class for implementing optimizers for multivariate functions.
 * It contains the boiler-plate code for initial guess and bounds
 * specifications.
 * <em>It is not a "user" class.</em>
 *
 * @param <PAIR> Type of the point/value pair returned by the optimization
 * algorithm.
 *
 * @since 3.1
 */
public abstract class BaseMultivariateOptimizer<PAIR>
    extends BaseOptimizer<PAIR> {
    /** Initial guess. */
    private double[] start;
    /** Lower bounds. */
    private double[] lowerBound;
    /** Upper bounds. */
    private double[] upperBound;

    /**
     * @param checker Convergence checker.
     */
    protected BaseMultivariateOptimizer(ConvergenceChecker<PAIR> checker) {
        super(checker);
    }

    /**
     * {@inheritDoc}
     *
     * @param optData Optimization data. In addition to those documented in
     * {@link BaseOptimizer#parseOptimizationData(OptimizationData[]) BaseOptimizer},
     * this method will register the following data:
     * <ul>
     *  <li>{@link InitialGuess}</li>
     *  <li>{@link SimpleBounds}</li>
     * </ul>
     * @return {@inheritDoc}
     */
    @Override
    public PAIR optimize(OptimizationData... optData) {
        // Perform optimization.
        return super.optimize(optData);
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
    @Override
    protected void parseOptimizationData(OptimizationData... optData) {
        // Allow base class to register its own data.
        super.parseOptimizationData(optData);

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

        // Check input consistency.
        checkParameters();
    }

    /**
     * Gets the initial guess.
     *
     * @return the initial guess, or {@code null} if not set.
     */
    public double[] getStartPoint() {
        return start == null ? null : start.clone();
    }
    /**
     * @return the lower bounds, or {@code null} if not set.
     */
    public double[] getLowerBound() {
        return lowerBound == null ? null : lowerBound.clone();
    }
    /**
     * @return the upper bounds, or {@code null} if not set.
     */
    public double[] getUpperBound() {
        return upperBound == null ? null : upperBound.clone();
    }

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
        }
    }
}
