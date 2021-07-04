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
import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.random.RandomGenerator;
import org.apache.commons.math3.random.Well19937c;
import org.apache.commons.math3.special.Gamma;
import org.apache.commons.math3.util.FastMath;

/**
 * Implementation of the Gamma distribution.
 *
 * @see <a href="http://en.wikipedia.org/wiki/Gamma_distribution">Gamma distribution (Wikipedia)</a>
 * @see <a href="http://mathworld.wolfram.com/GammaDistribution.html">Gamma distribution (MathWorld)</a>
 */
public class GammaDistribution extends AbstractRealDistribution {
    /**
     * Default inverse cumulative probability accuracy.
     * @since 2.1
     */
    public static final double DEFAULT_INVERSE_ABSOLUTE_ACCURACY = 1e-9;
    /** Serializable version identifier. */
    private static final long serialVersionUID = 20120524L;
    /** The shape parameter. */
    private final double shape;
    /** The scale parameter. */
    private final double scale;
    /**
     * The constant value of {@code shape + g + 0.5}, where {@code g} is the
     * Lanczos constant {@link Gamma#LANCZOS_G}.
     */
    private final double shiftedShape;
    /**
     * The constant value of
     * {@code shape / scale * sqrt(e / (2 * pi * (shape + g + 0.5))) / L(shape)},
     * where {@code L(shape)} is the Lanczos approximation returned by
     * {@link Gamma#lanczos(double)}. This prefactor is used in
     * {@link #density(double)}, when no overflow occurs with the natural
     * calculation.
     */
    private final double densityPrefactor1;
    /**
     * The constant value of
     * {@code log(shape / scale * sqrt(e / (2 * pi * (shape + g + 0.5))) / L(shape))},
     * where {@code L(shape)} is the Lanczos approximation returned by
     * {@link Gamma#lanczos(double)}. This prefactor is used in
     * {@link #logDensity(double)}, when no overflow occurs with the natural
     * calculation.
     */
    private final double logDensityPrefactor1;
    /**
     * The constant value of
     * {@code shape * sqrt(e / (2 * pi * (shape + g + 0.5))) / L(shape)},
     * where {@code L(shape)} is the Lanczos approximation returned by
     * {@link Gamma#lanczos(double)}. This prefactor is used in
     * {@link #density(double)}, when overflow occurs with the natural
     * calculation.
     */
    private final double densityPrefactor2;
    /**
     * The constant value of
     * {@code log(shape * sqrt(e / (2 * pi * (shape + g + 0.5))) / L(shape))},
     * where {@code L(shape)} is the Lanczos approximation returned by
     * {@link Gamma#lanczos(double)}. This prefactor is used in
     * {@link #logDensity(double)}, when overflow occurs with the natural
     * calculation.
     */
    private final double logDensityPrefactor2;
    /**
     * Lower bound on {@code y = x / scale} for the selection of the computation
     * method in {@link #density(double)}. For {@code y <= minY}, the natural
     * calculation overflows.
     */
    private final double minY;
    /**
     * Upper bound on {@code log(y)} ({@code y = x / scale}) for the selection
     * of the computation method in {@link #density(double)}. For
     * {@code log(y) >= maxLogY}, the natural calculation overflows.
     */
    private final double maxLogY;
    /** Inverse cumulative probability accuracy. */
    private final double solverAbsoluteAccuracy;

    /**
     * Creates a new gamma distribution with specified values of the shape and
     * scale parameters.
     * <p>
     * <b>Note:</b> this constructor will implicitly create an instance of
     * {@link Well19937c} as random generator to be used for sampling only (see
     * {@link #sample()} and {@link #sample(int)}). In case no sampling is
     * needed for the created distribution, it is advised to pass {@code null}
     * as random generator via the appropriate constructors to avoid the
     * additional initialisation overhead.
     *
     * @param shape the shape parameter
     * @param scale the scale parameter
     * @throws NotStrictlyPositiveException if {@code shape <= 0} or
     * {@code scale <= 0}.
     */
    public GammaDistribution(double shape, double scale) throws NotStrictlyPositiveException {
        this(shape, scale, DEFAULT_INVERSE_ABSOLUTE_ACCURACY);
    }

    /**
     * Creates a new gamma distribution with specified values of the shape and
     * scale parameters.
     * <p>
     * <b>Note:</b> this constructor will implicitly create an instance of
     * {@link Well19937c} as random generator to be used for sampling only (see
     * {@link #sample()} and {@link #sample(int)}). In case no sampling is
     * needed for the created distribution, it is advised to pass {@code null}
     * as random generator via the appropriate constructors to avoid the
     * additional initialisation overhead.
     *
     * @param shape the shape parameter
     * @param scale the scale parameter
     * @param inverseCumAccuracy the maximum absolute error in inverse
     * cumulative probability estimates (defaults to
     * {@link #DEFAULT_INVERSE_ABSOLUTE_ACCURACY}).
     * @throws NotStrictlyPositiveException if {@code shape <= 0} or
     * {@code scale <= 0}.
     * @since 2.1
     */
    public GammaDistribution(double shape, double scale, double inverseCumAccuracy)
        throws NotStrictlyPositiveException {
        this(new Well19937c(), shape, scale, inverseCumAccuracy);
    }

    /**
     * Creates a Gamma distribution.
     *
     * @param rng Random number generator.
     * @param shape the shape parameter
     * @param scale the scale parameter
     * @throws NotStrictlyPositiveException if {@code shape <= 0} or
     * {@code scale <= 0}.
     * @since 3.3
     */
    public GammaDistribution(RandomGenerator rng, double shape, double scale)
        throws NotStrictlyPositiveException {
        this(rng, shape, scale, DEFAULT_INVERSE_ABSOLUTE_ACCURACY);
    }

    /**
     * Creates a Gamma distribution.
     *
     * @param rng Random number generator.
     * @param shape the shape parameter
     * @param scale the scale parameter
     * @param inverseCumAccuracy the maximum absolute error in inverse
     * cumulative probability estimates (defaults to
     * {@link #DEFAULT_INVERSE_ABSOLUTE_ACCURACY}).
     * @throws NotStrictlyPositiveException if {@code shape <= 0} or
     * {@code scale <= 0}.
     * @since 3.1
     */
    public GammaDistribution(RandomGenerator rng,
                             double shape,
                             double scale,
                             double inverseCumAccuracy)
        throws NotStrictlyPositiveException {
        super(rng);

        if (shape <= 0) {
            throw new NotStrictlyPositiveException(LocalizedFormats.SHAPE, shape);
        }
        if (scale <= 0) {
            throw new NotStrictlyPositiveException(LocalizedFormats.SCALE, scale);
        }

        this.shape = shape;
        this.scale = scale;
        this.solverAbsoluteAccuracy = inverseCumAccuracy;
        this.shiftedShape = shape + Gamma.LANCZOS_G + 0.5;
        final double aux = FastMath.E / (2.0 * FastMath.PI * shiftedShape);
        this.densityPrefactor2 = shape * FastMath.sqrt(aux) / Gamma.lanczos(shape);
        this.logDensityPrefactor2 = FastMath.log(shape) + 0.5 * FastMath.log(aux) -
                                    FastMath.log(Gamma.lanczos(shape));
        this.densityPrefactor1 = this.densityPrefactor2 / scale *
                FastMath.pow(shiftedShape, -shape) *
                FastMath.exp(shape + Gamma.LANCZOS_G);
        this.logDensityPrefactor1 = this.logDensityPrefactor2 - FastMath.log(scale) -
                FastMath.log(shiftedShape) * shape +
                shape + Gamma.LANCZOS_G;
        this.minY = shape + Gamma.LANCZOS_G - FastMath.log(Double.MAX_VALUE);
        this.maxLogY = FastMath.log(Double.MAX_VALUE) / (shape - 1.0);
    }

    /**
     * Returns the shape parameter of {@code this} distribution.
     *
     * @return the shape parameter
     * @deprecated as of version 3.1, {@link #getShape()} should be preferred.
     * This method will be removed in version 4.0.
     */
    @Deprecated
    public double getAlpha() {
        return shape;
    }

    /**
     * Returns the shape parameter of {@code this} distribution.
     *
     * @return the shape parameter
     * @since 3.1
     */
    public double getShape() {
        return shape;
    }

    /**
     * Returns the scale parameter of {@code this} distribution.
     *
     * @return the scale parameter
     * @deprecated as of version 3.1, {@link #getScale()} should be preferred.
     * This method will be removed in version 4.0.
     */
    @Deprecated
    public double getBeta() {
        return scale;
    }

    /**
     * Returns the scale parameter of {@code this} distribution.
     *
     * @return the scale parameter
     * @since 3.1
     */
    public double getScale() {
        return scale;
    }

    /** {@inheritDoc} */
    public double density(double x) {
       /* The present method must return the value of
        *
        *     1       x a     - x
        * ---------- (-)  exp(---)
        * x Gamma(a)  b        b
        *
        * where a is the shape parameter, and b the scale parameter.
        * Substituting the Lanczos approximation of Gamma(a) leads to the
        * following expression of the density
        *
        * a              e            1         y      a
        * - sqrt(------------------) ---- (-----------)  exp(a - y + g),
        * x      2 pi (a + g + 0.5)  L(a)  a + g + 0.5
        *
        * where y = x / b. The above formula is the "natural" computation, which
        * is implemented when no overflow is likely to occur. If overflow occurs
        * with the natural computation, the following identity is used. It is
        * based on the BOOST library
        * http://www.boost.org/doc/libs/1_35_0/libs/math/doc/sf_and_dist/html/math_toolkit/special/sf_gamma/igamma.html
        * Formula (15) needs adaptations, which are detailed below.
        *
        *       y      a
        * (-----------)  exp(a - y + g)
        *  a + g + 0.5
        *                              y - a - g - 0.5    y (g + 0.5)
        *               = exp(a log1pm(---------------) - ----------- + g),
        *                                a + g + 0.5      a + g + 0.5
        *
        *  where log1pm(z) = log(1 + z) - z. Therefore, the value to be
        *  returned is
        *
        * a              e            1
        * - sqrt(------------------) ----
        * x      2 pi (a + g + 0.5)  L(a)
        *                              y - a - g - 0.5    y (g + 0.5)
        *               * exp(a log1pm(---------------) - ----------- + g).
        *                                a + g + 0.5      a + g + 0.5
        */
        if (x < 0) {
            return 0;
        }
        final double y = x / scale;
        if ((y <= minY) || (FastMath.log(y) >= maxLogY)) {
            /*
             * Overflow.
             */
            final double aux1 = (y - shiftedShape) / shiftedShape;
            final double aux2 = shape * (FastMath.log1p(aux1) - aux1);
            final double aux3 = -y * (Gamma.LANCZOS_G + 0.5) / shiftedShape +
                    Gamma.LANCZOS_G + aux2;
            return densityPrefactor2 / x * FastMath.exp(aux3);
        }
        /*
         * Natural calculation.
         */
        return densityPrefactor1 * FastMath.exp(-y) * FastMath.pow(y, shape - 1);
    }

    /** {@inheritDoc} **/
    @Override
    public double logDensity(double x) {
        /*
         * see the comment in {@link #density(double)} for computation details
         */
        if (x < 0) {
            return Double.NEGATIVE_INFINITY;
        }
        final double y = x / scale;
        if ((y <= minY) || (FastMath.log(y) >= maxLogY)) {
            /*
             * Overflow.
             */
            final double aux1 = (y - shiftedShape) / shiftedShape;
            final double aux2 = shape * (FastMath.log1p(aux1) - aux1);
            final double aux3 = -y * (Gamma.LANCZOS_G + 0.5) / shiftedShape +
                    Gamma.LANCZOS_G + aux2;
            return logDensityPrefactor2 - FastMath.log(x) + aux3;
        }
        /*
         * Natural calculation.
         */
        return logDensityPrefactor1 - y + FastMath.log(y) * (shape - 1);
    }

    /**
     * {@inheritDoc}
     *
     * The implementation of this method is based on:
     * <ul>
     *  <li>
     *   <a href="http://mathworld.wolfram.com/Chi-SquaredDistribution.html">
     *    Chi-Squared Distribution</a>, equation (9).
     *  </li>
     *  <li>Casella, G., & Berger, R. (1990). <i>Statistical Inference</i>.
     *    Belmont, CA: Duxbury Press.
     *  </li>
     * </ul>
     */
    public double cumulativeProbability(double x) {
        double ret;

        if (x <= 0) {
            ret = 0;
        } else {
            ret = Gamma.regularizedGammaP(shape, x / scale);
        }

        return ret;
    }

    /** {@inheritDoc} */
    @Override
    protected double getSolverAbsoluteAccuracy() {
        return solverAbsoluteAccuracy;
    }

    /**
     * {@inheritDoc}
     *
     * For shape parameter {@code alpha} and scale parameter {@code beta}, the
     * mean is {@code alpha * beta}.
     */
    public double getNumericalMean() {
        return shape * scale;
    }

    /**
     * {@inheritDoc}
     *
     * For shape parameter {@code alpha} and scale parameter {@code beta}, the
     * variance is {@code alpha * beta^2}.
     *
     * @return {@inheritDoc}
     */
    public double getNumericalVariance() {
        return shape * scale * scale;
    }

    /**
     * {@inheritDoc}
     *
     * The lower bound of the support is always 0 no matter the parameters.
     *
     * @return lower bound of the support (always 0)
     */
    public double getSupportLowerBound() {
        return 0;
    }

    /**
     * {@inheritDoc}
     *
     * The upper bound of the support is always positive infinity
     * no matter the parameters.
     *
     * @return upper bound of the support (always Double.POSITIVE_INFINITY)
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
     *
     * The support of this distribution is connected.
     *
     * @return {@code true}
     */
    public boolean isSupportConnected() {
        return true;
    }

    /**
     * <p>This implementation uses the following algorithms: </p>
     *
     * <p>For 0 < shape < 1: <br/>
     * Ahrens, J. H. and Dieter, U., <i>Computer methods for
     * sampling from gamma, beta, Poisson and binomial distributions.</i>
     * Computing, 12, 223-246, 1974.</p>
     *
     * <p>For shape >= 1: <br/>
     * Marsaglia and Tsang, <i>A Simple Method for Generating
     * Gamma Variables.</i> ACM Transactions on Mathematical Software,
     * Volume 26 Issue 3, September, 2000.</p>
     *
     * @return random value sampled from the Gamma(shape, scale) distribution
     */
    @Override
    public double sample()  {
        if (shape < 1) {
            // [1]: p. 228, Algorithm GS

            while (true) {
                // Step 1:
                final double u = random.nextDouble();
                final double bGS = 1 + shape / FastMath.E;
                final double p = bGS * u;

                if (p <= 1) {
                    // Step 2:

                    final double x = FastMath.pow(p, 1 / shape);
                    final double u2 = random.nextDouble();

                    if (u2 > FastMath.exp(-x)) {
                        // Reject
                        continue;
                    } else {
                        return scale * x;
                    }
                } else {
                    // Step 3:

                    final double x = -1 * FastMath.log((bGS - p) / shape);
                    final double u2 = random.nextDouble();

                    if (u2 > FastMath.pow(x, shape - 1)) {
                        // Reject
                        continue;
                    } else {
                        return scale * x;
                    }
                }
            }
        }

        // Now shape >= 1

        final double d = shape - 0.333333333333333333;
        final double c = 1 / (3 * FastMath.sqrt(d));

        while (true) {
            final double x = random.nextGaussian();
            final double v = (1 + c * x) * (1 + c * x) * (1 + c * x);

            if (v <= 0) {
                continue;
            }

            final double x2 = x * x;
            final double u = random.nextDouble();

            // Squeeze
            if (u < 1 - 0.0331 * x2 * x2) {
                return scale * d * v;
            }

            if (FastMath.log(u) < 0.5 * x2 + d * (1 - v + FastMath.log(v))) {
                return scale * d * v;
            }
        }
    }
}
