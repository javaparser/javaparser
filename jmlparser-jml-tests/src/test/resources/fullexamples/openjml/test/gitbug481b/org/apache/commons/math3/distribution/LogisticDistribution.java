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
import org.apache.commons.math3.exception.OutOfRangeException;
import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.random.RandomGenerator;
import org.apache.commons.math3.random.Well19937c;
import org.apache.commons.math3.util.FastMath;
import org.apache.commons.math3.util.MathUtils;

/**
 * This class implements the Logistic distribution.
 *
 * @see <a href="http://en.wikipedia.org/wiki/Logistic_distribution">Logistic Distribution (Wikipedia)</a>
 * @see <a href="http://mathworld.wolfram.com/LogisticDistribution.html">Logistic Distribution (Mathworld)</a>
 *
 * @since 3.4
 */
public class LogisticDistribution extends AbstractRealDistribution {

    /** Serializable version identifier. */
    private static final long serialVersionUID = 20141003;

    /** The location parameter. */
    private final double mu;
    /** The scale parameter. */
    private final double s;

    /**
     * Build a new instance.
     * <p>
     * <b>Note:</b> this constructor will implicitly create an instance of
     * {@link Well19937c} as random generator to be used for sampling only (see
     * {@link #sample()} and {@link #sample(int)}). In case no sampling is
     * needed for the created distribution, it is advised to pass {@code null}
     * as random generator via the appropriate constructors to avoid the
     * additional initialisation overhead.
     *
     * @param mu location parameter
     * @param s scale parameter (must be positive)
     * @throws NotStrictlyPositiveException if {@code beta <= 0}
     */
    public LogisticDistribution(double mu, double s) {
        this(new Well19937c(), mu, s);
    }

    /**
     * Build a new instance.
     *
     * @param rng Random number generator
     * @param mu location parameter
     * @param s scale parameter (must be positive)
     * @throws NotStrictlyPositiveException if {@code beta <= 0}
     */
    public LogisticDistribution(RandomGenerator rng, double mu, double s) {
        super(rng);

        if (s <= 0.0) {
            throw new NotStrictlyPositiveException(LocalizedFormats.NOT_POSITIVE_SCALE, s);
        }

        this.mu = mu;
        this.s = s;
    }

    /**
     * Access the location parameter, {@code mu}.
     *
     * @return the location parameter.
     */
    public double getLocation() {
        return mu;
    }

    /**
     * Access the scale parameter, {@code s}.
     *
     * @return the scale parameter.
     */
    public double getScale() {
        return s;
    }

    /** {@inheritDoc} */
    public double density(double x) {
        double z = (x - mu) / s;
        double v = FastMath.exp(-z);
        return 1 / s * v / ((1.0 + v) * (1.0 + v));
    }

    /** {@inheritDoc} */
    public double cumulativeProbability(double x) {
        double z = 1 / s * (x - mu);
        return 1.0 / (1.0 + FastMath.exp(-z));
    }

    /** {@inheritDoc} */
    @Override
    public double inverseCumulativeProbability(double p) throws OutOfRangeException {
        if (p < 0.0 || p > 1.0) {
            throw new OutOfRangeException(p, 0.0, 1.0);
        } else if (p == 0) {
            return 0.0;
        } else if (p == 1) {
            return Double.POSITIVE_INFINITY;
        }
        return s * Math.log(p / (1.0 - p)) + mu;
    }

    /** {@inheritDoc} */
    public double getNumericalMean() {
        return mu;
    }

    /** {@inheritDoc} */
    public double getNumericalVariance() {
        return (MathUtils.PI_SQUARED / 3.0) * (1.0 / (s * s));
    }

    /** {@inheritDoc} */
    public double getSupportLowerBound() {
        return Double.NEGATIVE_INFINITY;
    }

    /** {@inheritDoc} */
    public double getSupportUpperBound() {
        return Double.POSITIVE_INFINITY;
    }

    /** {@inheritDoc} */
    public boolean isSupportLowerBoundInclusive() {
        return false;
    }

    /** {@inheritDoc} */
    public boolean isSupportUpperBoundInclusive() {
        return false;
    }

    /** {@inheritDoc} */
    public boolean isSupportConnected() {
        return true;
    }

}
