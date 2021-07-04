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
package org.apache.commons.math3.fitting.leastsquares;

import org.apache.commons.math3.fitting.leastsquares.LeastSquaresOptimizer.Optimum;
import org.apache.commons.math3.fitting.leastsquares.LeastSquaresProblem.Evaluation;
import org.apache.commons.math3.linear.RealMatrix;
import org.apache.commons.math3.linear.RealVector;

/**
 * A pedantic implementation of {@link Optimum}.
 *
 * @since 3.3
 */
class OptimumImpl implements Optimum {

    /** abscissa and ordinate */
    private final Evaluation value;
    /** number of evaluations to compute this optimum */
    private final int evaluations;
    /** number of iterations to compute this optimum */
    private final int iterations;

    /**
     * Construct an optimum from an evaluation and the values of the counters.
     *
     * @param value       the function value
     * @param evaluations number of times the function was evaluated
     * @param iterations  number of iterations of the algorithm
     */
    OptimumImpl(final Evaluation value, final int evaluations, final int iterations) {
        this.value = value;
        this.evaluations = evaluations;
        this.iterations = iterations;
    }

    /* auto-generated implementations */

    /** {@inheritDoc} */
    public int getEvaluations() {
        return evaluations;
    }

    /** {@inheritDoc} */
    public int getIterations() {
        return iterations;
    }

    /** {@inheritDoc} */
    public RealMatrix getCovariances(double threshold) {
        return value.getCovariances(threshold);
    }

    /** {@inheritDoc} */
    public RealVector getSigma(double covarianceSingularityThreshold) {
        return value.getSigma(covarianceSingularityThreshold);
    }

    /** {@inheritDoc} */
    public double getRMS() {
        return value.getRMS();
    }

    /** {@inheritDoc} */
    public RealMatrix getJacobian() {
        return value.getJacobian();
    }

    /** {@inheritDoc} */
    public double getCost() {
        return value.getCost();
    }

    /** {@inheritDoc} */
    public RealVector getResiduals() {
        return value.getResiduals();
    }

    /** {@inheritDoc} */
    public RealVector getPoint() {
        return value.getPoint();
    }
}
