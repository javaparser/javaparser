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
package org.apache.commons.math3.analysis.integration;

import org.apache.commons.math3.analysis.UnivariateFunction;
import org.apache.commons.math3.analysis.integration.gauss.GaussIntegratorFactory;
import org.apache.commons.math3.analysis.integration.gauss.GaussIntegrator;
import org.apache.commons.math3.exception.MathIllegalArgumentException;
import org.apache.commons.math3.exception.MaxCountExceededException;
import org.apache.commons.math3.exception.NotStrictlyPositiveException;
import org.apache.commons.math3.exception.NumberIsTooSmallException;
import org.apache.commons.math3.exception.TooManyEvaluationsException;
import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.util.FastMath;

/**
 * This algorithm divides the integration interval into equally-sized
 * sub-interval and on each of them performs a
 * <a href="http://mathworld.wolfram.com/Legendre-GaussQuadrature.html">
 * Legendre-Gauss</a> quadrature.
 * Because of its <em>non-adaptive</em> nature, this algorithm can
 * converge to a wrong value for the integral (for example, if the
 * function is significantly different from zero toward the ends of the
 * integration interval).
 * In particular, a change of variables aimed at estimating integrals
 * over infinite intervals as proposed
 * <a href="http://en.wikipedia.org/w/index.php?title=Numerical_integration#Integrals_over_infinite_intervals">
 *  here</a> should be avoided when using this class.
 *
 * @since 3.1
 */

public class IterativeLegendreGaussIntegrator
    extends BaseAbstractUnivariateIntegrator {
    /** Factory that computes the points and weights. */
    private static final GaussIntegratorFactory FACTORY
        = new GaussIntegratorFactory();
    /** Number of integration points (per interval). */
    private final int numberOfPoints;

    /**
     * Builds an integrator with given accuracies and iterations counts.
     *
     * @param n Number of integration points.
     * @param relativeAccuracy Relative accuracy of the result.
     * @param absoluteAccuracy Absolute accuracy of the result.
     * @param minimalIterationCount Minimum number of iterations.
     * @param maximalIterationCount Maximum number of iterations.
     * @throws NotStrictlyPositiveException if minimal number of iterations
     * or number of points are not strictly positive.
     * @throws NumberIsTooSmallException if maximal number of iterations
     * is smaller than or equal to the minimal number of iterations.
     */
    public IterativeLegendreGaussIntegrator(final int n,
                                            final double relativeAccuracy,
                                            final double absoluteAccuracy,
                                            final int minimalIterationCount,
                                            final int maximalIterationCount)
        throws NotStrictlyPositiveException, NumberIsTooSmallException {
        super(relativeAccuracy, absoluteAccuracy, minimalIterationCount, maximalIterationCount);
        if (n <= 0) {
            throw new NotStrictlyPositiveException(LocalizedFormats.NUMBER_OF_POINTS, n);
        }
       numberOfPoints = n;
    }

    /**
     * Builds an integrator with given accuracies.
     *
     * @param n Number of integration points.
     * @param relativeAccuracy Relative accuracy of the result.
     * @param absoluteAccuracy Absolute accuracy of the result.
     * @throws NotStrictlyPositiveException if {@code n < 1}.
     */
    public IterativeLegendreGaussIntegrator(final int n,
                                            final double relativeAccuracy,
                                            final double absoluteAccuracy)
        throws NotStrictlyPositiveException {
        this(n, relativeAccuracy, absoluteAccuracy,
             DEFAULT_MIN_ITERATIONS_COUNT, DEFAULT_MAX_ITERATIONS_COUNT);
    }

    /**
     * Builds an integrator with given iteration counts.
     *
     * @param n Number of integration points.
     * @param minimalIterationCount Minimum number of iterations.
     * @param maximalIterationCount Maximum number of iterations.
     * @throws NotStrictlyPositiveException if minimal number of iterations
     * is not strictly positive.
     * @throws NumberIsTooSmallException if maximal number of iterations
     * is smaller than or equal to the minimal number of iterations.
     * @throws NotStrictlyPositiveException if {@code n < 1}.
     */
    public IterativeLegendreGaussIntegrator(final int n,
                                            final int minimalIterationCount,
                                            final int maximalIterationCount)
        throws NotStrictlyPositiveException, NumberIsTooSmallException {
        this(n, DEFAULT_RELATIVE_ACCURACY, DEFAULT_ABSOLUTE_ACCURACY,
             minimalIterationCount, maximalIterationCount);
    }

    /** {@inheritDoc} */
    @Override
    protected double doIntegrate()
        throws MathIllegalArgumentException, TooManyEvaluationsException, MaxCountExceededException {
        // Compute first estimate with a single step.
        double oldt = stage(1);

        int n = 2;
        while (true) {
            // Improve integral with a larger number of steps.
            final double t = stage(n);

            // Estimate the error.
            final double delta = FastMath.abs(t - oldt);
            final double limit =
                FastMath.max(getAbsoluteAccuracy(),
                             getRelativeAccuracy() * (FastMath.abs(oldt) + FastMath.abs(t)) * 0.5);

            // check convergence
            if (getIterations() + 1 >= getMinimalIterationCount() &&
                delta <= limit) {
                return t;
            }

            // Prepare next iteration.
            final double ratio = FastMath.min(4, FastMath.pow(delta / limit, 0.5 / numberOfPoints));
            n = FastMath.max((int) (ratio * n), n + 1);
            oldt = t;
            incrementCount();
        }
    }

    /**
     * Compute the n-th stage integral.
     *
     * @param n Number of steps.
     * @return the value of n-th stage integral.
     * @throws TooManyEvaluationsException if the maximum number of evaluations
     * is exceeded.
     */
    private double stage(final int n)
        throws TooManyEvaluationsException {
        // Function to be integrated is stored in the base class.
        final UnivariateFunction f = new UnivariateFunction() {
                /** {@inheritDoc} */
                public double value(double x)
                    throws MathIllegalArgumentException, TooManyEvaluationsException {
                    return computeObjectiveValue(x);
                }
            };

        final double min = getMin();
        final double max = getMax();
        final double step = (max - min) / n;

        double sum = 0;
        for (int i = 0; i < n; i++) {
            // Integrate over each sub-interval [a, b].
            final double a = min + i * step;
            final double b = a + step;
            final GaussIntegrator g = FACTORY.legendreHighPrecision(numberOfPoints, a, b);
            sum += g.integrate(f);
        }

        return sum;
    }
}
