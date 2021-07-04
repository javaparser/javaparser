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

import org.apache.commons.math3.fitting.leastsquares.LeastSquaresProblem.Evaluation;
import org.apache.commons.math3.optim.ConvergenceChecker;
import org.apache.commons.math3.util.Precision;

/**
 * Check if an optimization has converged based on the change in computed RMS.
 *
 * @since 3.4
 */
public class EvaluationRmsChecker implements ConvergenceChecker<Evaluation> {

    /** relative tolerance for comparisons. */
    private final double relTol;
    /** absolute tolerance for comparisons. */
    private final double absTol;

    /**
     * Create a convergence checker for the RMS with the same relative and absolute
     * tolerance.
     *
     * <p>Convenience constructor for when the relative and absolute tolerances are the
     * same. Same as {@code new EvaluationRmsChecker(tol, tol)}.
     *
     * @param tol the relative and absolute tolerance.
     * @see #EvaluationRmsChecker(double, double)
     */
    public EvaluationRmsChecker(final double tol) {
        this(tol, tol);
    }

    /**
     * Create a convergence checker for the RMS with a relative and absolute tolerance.
     *
     * <p>The optimization has converged when the RMS of consecutive evaluations are equal
     * to within the given relative tolerance or absolute tolerance.
     *
     * @param relTol the relative tolerance.
     * @param absTol the absolute tolerance.
     * @see Precision#equals(double, double, double)
     * @see Precision#equalsWithRelativeTolerance(double, double, double)
     */
    public EvaluationRmsChecker(final double relTol, final double absTol) {
        this.relTol = relTol;
        this.absTol = absTol;
    }

    /** {@inheritDoc} */
    public boolean converged(final int iteration,
                             final Evaluation previous,
                             final Evaluation current) {
        final double prevRms = previous.getRMS();
        final double currRms = current.getRMS();
        return Precision.equals(prevRms, currRms, this.absTol) ||
                Precision.equalsWithRelativeTolerance(prevRms, currRms, this.relTol);
    }

}
