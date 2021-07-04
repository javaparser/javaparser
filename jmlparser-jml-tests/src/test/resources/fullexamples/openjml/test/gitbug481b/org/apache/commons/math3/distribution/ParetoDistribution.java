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

import org.apache.commons.math3.exception.NotStrictlyPositiveException;
import org.apache.commons.math3.exception.NumberIsTooLargeException;
import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.random.RandomGenerator;
import org.apache.commons.math3.random.Well19937c;
import org.apache.commons.math3.util.FastMath;

/**
 * Implementation of the Pareto distribution.
 *
 * <p>
 * <strong>Parameters:</strong>
 * The probability distribution function of {@code X} is given by (for {@code x >= k}):
 * <pre>
 *  α * k^α / x^(α + 1)
 * </pre>
 * <p>
 * <ul>
 * <li>{@code k} is the <em>scale</em> parameter: this is the minimum possible value of {@code X},</li>
 * <li>{@code α} is the <em>shape</em> parameter: this is the Pareto index</li>
 * </ul>
 *
 * @see <a href="http://en.wikipedia.org/wiki/Pareto_distribution">
 * Pareto distribution (Wikipedia)</a>
 * @see <a href="http://mathworld.wolfram.com/ParetoDistribution.html">
 * Pareto distribution (MathWorld)</a>
 *
 * @since 3.3
 */
public class ParetoDistribution extends AbstractRealDistribution {

    /** Default inverse cumulative probability accuracy. */
    public static final double DEFAULT_INVERSE_ABSOLUTE_ACCURACY = 1e-9;

    /** Serializable version identifier. */
    private static final long serialVersionUID = 20130424;

    /** The scale parameter of this distribution. */
    private final double scale;

    /** The shape parameter of this distribution. */
    private final double shape;

    /** Inverse cumulative probability accuracy. */
    private final double solverAbsoluteAccuracy;

    /**
     * Create a Pareto distribution with a scale of {@code 1} and a shape of {@code 1}.
     */
    public ParetoDistribution() {
        this(1, 1);
    }

    /**
     * Create a Pareto distribution using the specified scale and shape.
     * <p>
     * <b>Note:</b> this constructor will implicitly create an instance of
     * {@link Well19937c} as random generator to be used for sampling only (see
     * {@link #sample()} and {@link #sample(int)}). In case no sampling is
     * needed for the created distribution, it is advised to pass {@code null}
     * as random generator via the appropriate constructors to avoid the
     * additional initialisation overhead.
     *
     * @param scale the scale parameter of this distribution
     * @param shape the shape parameter of this distribution
     * @throws NotStrictlyPositiveException if {@code scale <= 0} or {@code shape <= 0}.
     */
    public ParetoDistribution(double scale, double shape)
        throws NotStrictlyPositiveException {
        this(scale, shape, DEFAULT_INVERSE_ABSOLUTE_ACCURACY);
    }

    /**
     * Create a Pareto distribution using the specified scale, shape and
     * inverse cumulative distribution accuracy.
     * <p>
     * <b>Note:</b> this constructor will implicitly create an instance of
     * {@link Well19937c} as random generator to be used for sampling only (see
     * {@link #sample()} and {@link #sample(int)}). In case no sampling is
     * needed for the created distribution, it is advised to pass {@code null}
     * as random generator via the appropriate constructors to avoid the
     * additional initialisation overhead.
     *
     * @param scale the scale parameter of this distribution
     * @param shape the shape parameter of this distribution
     * @param inverseCumAccuracy Inverse cumulative probability accuracy.
     * @throws NotStrictlyPositiveException if {@code scale <= 0} or {@code shape <= 0}.
     */
    public ParetoDistribution(double scale, double shape, double inverseCumAccuracy)
        throws NotStrictlyPositiveException {
        this(new Well19937c(), scale, shape, inverseCumAccuracy);
    }

    /**
     * Creates a Pareto distribution.
     *
     * @param rng Random number generator.
     * @param scale Scale parameter of this distribution.
     * @param shape Shape parameter of this distribution.
     * @throws NotStrictlyPositiveException if {@code scale <= 0} or {@code shape <= 0}.
     */
    public ParetoDistribution(RandomGenerator rng, double scale, double shape)
        throws NotStrictlyPositiveException {
        this(rng, scale, shape, DEFAULT_INVERSE_ABSOLUTE_ACCURACY);
    }

    /**
     * Creates a Pareto distribution.
     *
     * @param rng Random number generator.
     * @param scale Scale parameter of this distribution.
     * @param shape Shape parameter of this distribution.
     * @param inverseCumAccuracy Inverse cumulative probability accuracy.
     * @throws NotStrictlyPositiveException if {@code scale <= 0} or {@code shape <= 0}.
     */
    public ParetoDistribution(RandomGenerator rng,
                              double scale,
                              double shape,
                              double inverseCumAccuracy)
        throws NotStrictlyPositiveException {
        super(rng);

        if (scale <= 0) {
            throw new NotStrictlyPositiveException(LocalizedFormats.SCALE, scale);
        }

        if (shape <= 0) {
            throw new NotStrictlyPositiveException(LocalizedFormats.SHAPE, shape);
        }

        this.scale = scale;
        this.shape = shape;
        this.solverAbsoluteAccuracy = inverseCumAccuracy;
    }

    /**
     * Returns the scale parameter of this distribution.
     *
     * @return the scale parameter
     */
    public double getScale() {
        return scale;
    }

    /**
     * Returns the shape parameter of this distribution.
     *
     * @return the shape parameter
     */
    public double getShape() {
        return shape;
    }

    /**
     * {@inheritDoc}
     * <p>
     * For scale {@code k}, and shape {@code α} of this distribution, the PDF
     * is given by
     * <ul>
     * <li>{@code 0} if {@code x < k},</li>
     * <li>{@code α * k^α / x^(α + 1)} otherwise.</li>
     * </ul>
     */
    public double density(double x) {
        if (x < scale) {
            return 0;
        }
        return FastMath.pow(scale, shape) / FastMath.pow(x, shape + 1) * shape;
    }

    /** {@inheritDoc}
     *
     * See documentation of {@link #density(double)} for computation details.
     */
    @Override
    public double logDensity(double x) {
        if (x < scale) {
            return Double.NEGATIVE_INFINITY;
        }
        return FastMath.log(scale) * shape - FastMath.log(x) * (shape + 1) + FastMath.log(shape);
    }

    /**
     * {@inheritDoc}
     * <p>
     * For scale {@code k}, and shape {@code α} of this distribution, the CDF is given by
     * <ul>
     * <li>{@code 0} if {@code x < k},</li>
     * <li>{@code 1 - (k / x)^α} otherwise.</li>
     * </ul>
     */
    public double cumulativeProbability(double x)  {
        if (x <= scale) {
            return 0;
        }
        return 1 - FastMath.pow(scale / x, shape);
    }

    /**
     * {@inheritDoc}
     *
     * @deprecated See {@link RealDistribution#cumulativeProbability(double,double)}
     */
    @Override
    @Deprecated
    public double cumulativeProbability(double x0, double x1)
        throws NumberIsTooLargeException {
        return probability(x0, x1);
    }

    /** {@inheritDoc} */
    @Override
    protected double getSolverAbsoluteAccuracy() {
        return solverAbsoluteAccuracy;
    }

    /**
     * {@inheritDoc}
     * <p>
     * For scale {@code k} and shape {@code α}, the mean is given by
     * <ul>
     * <li>{@code ∞} if {@code α <= 1},</li>
     * <li>{@code α * k / (α - 1)} otherwise.</li>
     * </ul>
     */
    public double getNumericalMean() {
        if (shape <= 1) {
            return Double.POSITIVE_INFINITY;
        }
        return shape * scale / (shape - 1);
    }

    /**
     * {@inheritDoc}
     * <p>
     * For scale {@code k} and shape {@code α}, the variance is given by
     * <ul>
     * <li>{@code ∞} if {@code 1 < α <= 2},</li>
     * <li>{@code k^2 * α / ((α - 1)^2 * (α - 2))} otherwise.</li>
     * </ul>
     */
    public double getNumericalVariance() {
        if (shape <= 2) {
            return Double.POSITIVE_INFINITY;
        }
        double s = shape - 1;
        return scale * scale * shape / (s * s) / (shape - 2);
    }

    /**
     * {@inheritDoc}
     * <p>
     * The lower bound of the support is equal to the scale parameter {@code k}.
     *
     * @return lower bound of the support
     */
    public double getSupportLowerBound() {
        return scale;
    }

    /**
     * {@inheritDoc}
     * <p>
     * The upper bound of the support is always positive infinity no matter the parameters.
     *
     * @return upper bound of the support (always {@code Double.POSITIVE_INFINITY})
     */
    public double getSupportUpperBound() {
        return Double.POSITIVE_INFINITY;
    }

    /** {@inheritDoc} */
    public boolean isSupportLowerBoundInclusive() {
        return true;
    }

    /** {@inheritDoc} */
    public boolean isSupportUpperBoundInclusive() {
        return false;
    }

    /**
     * {@inheritDoc}
     * <p>
     * The support of this distribution is connected.
     *
     * @return {@code true}
     */
    public boolean isSupportConnected() {
        return true;
    }

    /** {@inheritDoc} */
    @Override
    public double sample()  {
        final double n = random.nextDouble();
        return scale / FastMath.pow(n, 1 / shape);
    }
}
