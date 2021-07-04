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

package org.apache.commons.math3.distribution;

import org.apache.commons.math3.exception.NumberIsTooLargeException;
import org.apache.commons.math3.exception.NumberIsTooSmallException;
import org.apache.commons.math3.exception.OutOfRangeException;
import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.random.RandomGenerator;
import org.apache.commons.math3.random.Well19937c;
import org.apache.commons.math3.util.FastMath;

/**
 * Implementation of the triangular real distribution.
 *
 * @see <a href="http://en.wikipedia.org/wiki/Triangular_distribution">
 * Triangular distribution (Wikipedia)</a>
 *
 * @since 3.0
 */
public class TriangularDistribution extends AbstractRealDistribution {
    /** Serializable version identifier. */
    private static final long serialVersionUID = 20120112L;
    /** Lower limit of this distribution (inclusive). */
    private final double a;
    /** Upper limit of this distribution (inclusive). */
    private final double b;
    /** Mode of this distribution. */
    private final double c;
    /** Inverse cumulative probability accuracy. */
    private final double solverAbsoluteAccuracy;

    /**
     * Creates a triangular real distribution using the given lower limit,
     * upper limit, and mode.
     * <p>
     * <b>Note:</b> this constructor will implicitly create an instance of
     * {@link Well19937c} as random generator to be used for sampling only (see
     * {@link #sample()} and {@link #sample(int)}). In case no sampling is
     * needed for the created distribution, it is advised to pass {@code null}
     * as random generator via the appropriate constructors to avoid the
     * additional initialisation overhead.
     *
     * @param a Lower limit of this distribution (inclusive).
     * @param b Upper limit of this distribution (inclusive).
     * @param c Mode of this distribution.
     * @throws NumberIsTooLargeException if {@code a >= b} or if {@code c > b}.
     * @throws NumberIsTooSmallException if {@code c < a}.
     */
    public TriangularDistribution(double a, double c, double b)
        throws NumberIsTooLargeException, NumberIsTooSmallException {
        this(new Well19937c(), a, c, b);
    }

    /**
     * Creates a triangular distribution.
     *
     * @param rng Random number generator.
     * @param a Lower limit of this distribution (inclusive).
     * @param b Upper limit of this distribution (inclusive).
     * @param c Mode of this distribution.
     * @throws NumberIsTooLargeException if {@code a >= b} or if {@code c > b}.
     * @throws NumberIsTooSmallException if {@code c < a}.
     * @since 3.1
     */
    public TriangularDistribution(RandomGenerator rng,
                                  double a,
                                  double c,
                                  double b)
        throws NumberIsTooLargeException, NumberIsTooSmallException {
        super(rng);

        if (a >= b) {
            throw new NumberIsTooLargeException(
                            LocalizedFormats.LOWER_BOUND_NOT_BELOW_UPPER_BOUND,
                            a, b, false);
        }
        if (c < a) {
            throw new NumberIsTooSmallException(
                    LocalizedFormats.NUMBER_TOO_SMALL, c, a, true);
        }
        if (c > b) {
            throw new NumberIsTooLargeException(
                    LocalizedFormats.NUMBER_TOO_LARGE, c, b, true);
        }

        this.a = a;
        this.c = c;
        this.b = b;
        solverAbsoluteAccuracy = FastMath.max(FastMath.ulp(a), FastMath.ulp(b));
    }

    /**
     * Returns the mode {@code c} of this distribution.
     *
     * @return the mode {@code c} of this distribution
     */
    public double getMode() {
        return c;
    }

    /**
     * {@inheritDoc}
     *
     * <p>
     * For this distribution, the returned value is not really meaningful,
     * since exact formulas are implemented for the computation of the
     * {@link #inverseCumulativeProbability(double)} (no solver is invoked).
     * </p>
     * <p>
     * For lower limit {@code a} and upper limit {@code b}, the current
     * implementation returns {@code max(ulp(a), ulp(b)}.
     * </p>
     */
    @Override
    protected double getSolverAbsoluteAccuracy() {
        return solverAbsoluteAccuracy;
    }

    /**
     * {@inheritDoc}
     *
     * For lower limit {@code a}, upper limit {@code b} and mode {@code c}, the
     * PDF is given by
     * <ul>
     * <li>{@code 2 * (x - a) / [(b - a) * (c - a)]} if {@code a <= x < c},</li>
     * <li>{@code 2 / (b - a)} if {@code x = c},</li>
     * <li>{@code 2 * (b - x) / [(b - a) * (b - c)]} if {@code c < x <= b},</li>
     * <li>{@code 0} otherwise.
     * </ul>
     */
    public double density(double x) {
        if (x < a) {
            return 0;
        }
        if (a <= x && x < c) {
            double divident = 2 * (x - a);
            double divisor = (b - a) * (c - a);
            return divident / divisor;
        }
        if (x == c) {
            return 2 / (b - a);
        }
        if (c < x && x <= b) {
            double divident = 2 * (b - x);
            double divisor = (b - a) * (b - c);
            return divident / divisor;
        }
        return 0;
    }

    /**
     * {@inheritDoc}
     *
     * For lower limit {@code a}, upper limit {@code b} and mode {@code c}, the
     * CDF is given by
     * <ul>
     * <li>{@code 0} if {@code x < a},</li>
     * <li>{@code (x - a)^2 / [(b - a) * (c - a)]} if {@code a <= x < c},</li>
     * <li>{@code (c - a) / (b - a)} if {@code x = c},</li>
     * <li>{@code 1 - (b - x)^2 / [(b - a) * (b - c)]} if {@code c < x <= b},</li>
     * <li>{@code 1} if {@code x > b}.</li>
     * </ul>
     */
    public double cumulativeProbability(double x)  {
        if (x < a) {
            return 0;
        }
        if (a <= x && x < c) {
            double divident = (x - a) * (x - a);
            double divisor = (b - a) * (c - a);
            return divident / divisor;
        }
        if (x == c) {
            return (c - a) / (b - a);
        }
        if (c < x && x <= b) {
            double divident = (b - x) * (b - x);
            double divisor = (b - a) * (b - c);
            return 1 - (divident / divisor);
        }
        return 1;
    }

    /**
     * {@inheritDoc}
     *
     * For lower limit {@code a}, upper limit {@code b}, and mode {@code c},
     * the mean is {@code (a + b + c) / 3}.
     */
    public double getNumericalMean() {
        return (a + b + c) / 3;
    }

    /**
     * {@inheritDoc}
     *
     * For lower limit {@code a}, upper limit {@code b}, and mode {@code c},
     * the variance is {@code (a^2 + b^2 + c^2 - a * b - a * c - b * c) / 18}.
     */
    public double getNumericalVariance() {
        return (a * a + b * b + c * c - a * b - a * c - b * c) / 18;
    }

    /**
     * {@inheritDoc}
     *
     * The lower bound of the support is equal to the lower limit parameter
     * {@code a} of the distribution.
     *
     * @return lower bound of the support
     */
    public double getSupportLowerBound() {
        return a;
    }

    /**
     * {@inheritDoc}
     *
     * The upper bound of the support is equal to the upper limit parameter
     * {@code b} of the distribution.
     *
     * @return upper bound of the support
     */
    public double getSupportUpperBound() {
        return b;
    }

    /** {@inheritDoc} */
    public boolean isSupportLowerBoundInclusive() {
        return true;
    }

    /** {@inheritDoc} */
    public boolean isSupportUpperBoundInclusive() {
        return true;
    }

    /**
     * {@inheritDoc}
     *
     * The support of this distribution is connected.
     *
     * @return {@code true}
     */
    public boolean isSupportConnected() {
        return true;
    }

    /** {@inheritDoc} */
    @Override
    public double inverseCumulativeProbability(double p)
        throws OutOfRangeException {
        if (p < 0 || p > 1) {
            throw new OutOfRangeException(p, 0, 1);
        }
        if (p == 0) {
            return a;
        }
        if (p == 1) {
            return b;
        }
        if (p < (c - a) / (b - a)) {
            return a + FastMath.sqrt(p * (b - a) * (c - a));
        }
        return b - FastMath.sqrt((1 - p) * (b - a) * (b - c));
    }
}
