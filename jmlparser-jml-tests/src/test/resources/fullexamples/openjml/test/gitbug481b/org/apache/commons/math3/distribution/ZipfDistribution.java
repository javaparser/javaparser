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
import org.apache.commons.math3.util.FastMath;

/**
 * Implementation of the Zipf distribution.
 * <p>
 * <strong>Parameters:</strong>
 * For a random variable {@code X} whose values are distributed according to this
 * distribution, the probability mass function is given by
 * <pre>
 *   P(X = k) = H(N,s) * 1 / k^s    for {@code k = 1,2,...,N}.
 * </pre>
 * {@code H(N,s)} is the normalizing constant
 * which corresponds to the generalized harmonic number of order N of s.
 * <p>
 * <ul>
 * <li>{@code N} is the number of elements</li>
 * <li>{@code s} is the exponent</li>
 * </ul>
 * @see <a href="https://en.wikipedia.org/wiki/Zipf's_law">Zipf's law (Wikipedia)</a>
 * @see <a href="https://en.wikipedia.org/wiki/Harmonic_number#Generalized_harmonic_numbers">Generalized harmonic numbers</a>
 */
public class ZipfDistribution extends AbstractIntegerDistribution {
    /** Serializable version identifier. */
    private static final long serialVersionUID = -140627372283420404L;
    /** Number of elements. */
    private final int numberOfElements;
    /** Exponent parameter of the distribution. */
    private final double exponent;
    /** Cached numerical mean */
    private double numericalMean = Double.NaN;
    /** Whether or not the numerical mean has been calculated */
    private boolean numericalMeanIsCalculated = false;
    /** Cached numerical variance */
    private double numericalVariance = Double.NaN;
    /** Whether or not the numerical variance has been calculated */
    private boolean numericalVarianceIsCalculated = false;
    /** The sampler to be used for the sample() method */
    private transient ZipfRejectionInversionSampler sampler;

    /**
     * Create a new Zipf distribution with the given number of elements and
     * exponent.
     * <p>
     * <b>Note:</b> this constructor will implicitly create an instance of
     * {@link Well19937c} as random generator to be used for sampling only (see
     * {@link #sample()} and {@link #sample(int)}). In case no sampling is
     * needed for the created distribution, it is advised to pass {@code null}
     * as random generator via the appropriate constructors to avoid the
     * additional initialisation overhead.
     *
     * @param numberOfElements Number of elements.
     * @param exponent Exponent.
     * @exception NotStrictlyPositiveException if {@code numberOfElements <= 0}
     * or {@code exponent <= 0}.
     */
    public ZipfDistribution(final int numberOfElements, final double exponent) {
        this(new Well19937c(), numberOfElements, exponent);
    }

    /**
     * Creates a Zipf distribution.
     *
     * @param rng Random number generator.
     * @param numberOfElements Number of elements.
     * @param exponent Exponent.
     * @exception NotStrictlyPositiveException if {@code numberOfElements <= 0}
     * or {@code exponent <= 0}.
     * @since 3.1
     */
    public ZipfDistribution(RandomGenerator rng,
                            int numberOfElements,
                            double exponent)
        throws NotStrictlyPositiveException {
        super(rng);

        if (numberOfElements <= 0) {
            throw new NotStrictlyPositiveException(LocalizedFormats.DIMENSION,
                                                   numberOfElements);
        }
        if (exponent <= 0) {
            throw new NotStrictlyPositiveException(LocalizedFormats.EXPONENT,
                                                   exponent);
        }

        this.numberOfElements = numberOfElements;
        this.exponent = exponent;
    }

    /**
     * Get the number of elements (e.g. corpus size) for the distribution.
     *
     * @return the number of elements
     */
    public int getNumberOfElements() {
        return numberOfElements;
    }

    /**
     * Get the exponent characterizing the distribution.
     *
     * @return the exponent
     */
    public double getExponent() {
        return exponent;
    }

    /** {@inheritDoc} */
    public double probability(final int x) {
        if (x <= 0 || x > numberOfElements) {
            return 0.0;
        }

        return (1.0 / FastMath.pow(x, exponent)) / generalizedHarmonic(numberOfElements, exponent);
    }

    /** {@inheritDoc} */
    @Override
    public double logProbability(int x) {
        if (x <= 0 || x > numberOfElements) {
            return Double.NEGATIVE_INFINITY;
        }

        return -FastMath.log(x) * exponent - FastMath.log(generalizedHarmonic(numberOfElements, exponent));
    }

    /** {@inheritDoc} */
    public double cumulativeProbability(final int x) {
        if (x <= 0) {
            return 0.0;
        } else if (x >= numberOfElements) {
            return 1.0;
        }

        return generalizedHarmonic(x, exponent) / generalizedHarmonic(numberOfElements, exponent);
    }

    /**
     * {@inheritDoc}
     *
     * For number of elements {@code N} and exponent {@code s}, the mean is
     * {@code Hs1 / Hs}, where
     * <ul>
     *  <li>{@code Hs1 = generalizedHarmonic(N, s - 1)},</li>
     *  <li>{@code Hs = generalizedHarmonic(N, s)}.</li>
     * </ul>
     */
    public double getNumericalMean() {
        if (!numericalMeanIsCalculated) {
            numericalMean = calculateNumericalMean();
            numericalMeanIsCalculated = true;
        }
        return numericalMean;
    }

    /**
     * Used by {@link #getNumericalMean()}.
     *
     * @return the mean of this distribution
     */
    protected double calculateNumericalMean() {
        final int N = getNumberOfElements();
        final double s = getExponent();

        final double Hs1 = generalizedHarmonic(N, s - 1);
        final double Hs = generalizedHarmonic(N, s);

        return Hs1 / Hs;
    }

    /**
     * {@inheritDoc}
     *
     * For number of elements {@code N} and exponent {@code s}, the mean is
     * {@code (Hs2 / Hs) - (Hs1^2 / Hs^2)}, where
     * <ul>
     *  <li>{@code Hs2 = generalizedHarmonic(N, s - 2)},</li>
     *  <li>{@code Hs1 = generalizedHarmonic(N, s - 1)},</li>
     *  <li>{@code Hs = generalizedHarmonic(N, s)}.</li>
     * </ul>
     */
    public double getNumericalVariance() {
        if (!numericalVarianceIsCalculated) {
            numericalVariance = calculateNumericalVariance();
            numericalVarianceIsCalculated = true;
        }
        return numericalVariance;
    }

    /**
     * Used by {@link #getNumericalVariance()}.
     *
     * @return the variance of this distribution
     */
    protected double calculateNumericalVariance() {
        final int N = getNumberOfElements();
        final double s = getExponent();

        final double Hs2 = generalizedHarmonic(N, s - 2);
        final double Hs1 = generalizedHarmonic(N, s - 1);
        final double Hs = generalizedHarmonic(N, s);

        return (Hs2 / Hs) - ((Hs1 * Hs1) / (Hs * Hs));
    }

    /**
     * Calculates the Nth generalized harmonic number. See
     * <a href="http://mathworld.wolfram.com/HarmonicSeries.html">Harmonic
     * Series</a>.
     *
     * @param n Term in the series to calculate (must be larger than 1)
     * @param m Exponent (special case {@code m = 1} is the harmonic series).
     * @return the n<sup>th</sup> generalized harmonic number.
     */
    private double generalizedHarmonic(final int n, final double m) {
        double value = 0;
        for (int k = n; k > 0; --k) {
            value += 1.0 / FastMath.pow(k, m);
        }
        return value;
    }

    /**
     * {@inheritDoc}
     *
     * The lower bound of the support is always 1 no matter the parameters.
     *
     * @return lower bound of the support (always 1)
     */
    public int getSupportLowerBound() {
        return 1;
    }

    /**
     * {@inheritDoc}
     *
     * The upper bound of the support is the number of elements.
     *
     * @return upper bound of the support
     */
    public int getSupportUpperBound() {
        return getNumberOfElements();
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
     * {@inheritDoc}
     */
    @Override
    public int sample() {
        if (sampler == null) {
            sampler = new ZipfRejectionInversionSampler(numberOfElements, exponent);
        }
        return sampler.sample(random);
    }

    /**
     * Utility class implementing a rejection inversion sampling method for a discrete,
     * bounded Zipf distribution that is based on the method described in
     * <p>
     * Wolfgang Hörmann and Gerhard Derflinger
     * "Rejection-inversion to generate variates from monotone discrete distributions."
     * ACM Transactions on Modeling and Computer Simulation (TOMACS) 6.3 (1996): 169-184.
     * <p>
     * The paper describes an algorithm for exponents larger than 1 (Algorithm ZRI).
     * The original method uses {@code H(x) := (v + x)^(1 - q) / (1 - q)}
     * as the integral of the hat function. This function is undefined for
     * q = 1, which is the reason for the limitation of the exponent.
     * If instead the integral function
     * {@code H(x) := ((v + x)^(1 - q) - 1) / (1 - q)} is used,
     * for which a meaningful limit exists for q = 1,
     * the method works for all positive exponents.
     * <p>
     * The following implementation uses v := 0 and generates integral numbers
     * in the range [1, numberOfElements]. This is different to the original method
     * where v is defined to be positive and numbers are taken from [0, i_max].
     * This explains why the implementation looks slightly different.
     *
     * @since 3.6
     */
    static final class ZipfRejectionInversionSampler {

        /** Exponent parameter of the distribution. */
        private final double exponent;
        /** Number of elements. */
        private final int numberOfElements;
        /** Constant equal to {@code hIntegral(1.5) - 1}. */
        private final double hIntegralX1;
        /** Constant equal to {@code hIntegral(numberOfElements + 0.5)}. */
        private final double hIntegralNumberOfElements;
        /** Constant equal to {@code 2 - hIntegralInverse(hIntegral(2.5) - h(2)}. */
        private final double s;

        /** Simple constructor.
         * @param numberOfElements number of elements
         * @param exponent exponent parameter of the distribution
         */
        ZipfRejectionInversionSampler(final int numberOfElements, final double exponent) {
            this.exponent = exponent;
            this.numberOfElements = numberOfElements;
            this.hIntegralX1 = hIntegral(1.5) - 1d;
            this.hIntegralNumberOfElements = hIntegral(numberOfElements + 0.5);
            this.s = 2d - hIntegralInverse(hIntegral(2.5) - h(2));
        }

        /** Generate one integral number in the range [1, numberOfElements].
         * @param random random generator to use
         * @return generated integral number in the range [1, numberOfElements]
         */
        int sample(final RandomGenerator random) {
            while(true) {

                final double u = hIntegralNumberOfElements + random.nextDouble() * (hIntegralX1 - hIntegralNumberOfElements);
                // u is uniformly distributed in (hIntegralX1, hIntegralNumberOfElements]

                double x = hIntegralInverse(u);

                int k = (int)(x + 0.5);

                // Limit k to the range [1, numberOfElements]
                // (k could be outside due to numerical inaccuracies)
                if (k < 1) {
                    k = 1;
                }
                else if (k > numberOfElements) {
                    k = numberOfElements;
                }

                // Here, the distribution of k is given by:
                //
                //   P(k = 1) = C * (hIntegral(1.5) - hIntegralX1) = C
                //   P(k = m) = C * (hIntegral(m + 1/2) - hIntegral(m - 1/2)) for m >= 2
                //
                //   where C := 1 / (hIntegralNumberOfElements - hIntegralX1)

                if (k - x <= s || u >= hIntegral(k + 0.5) - h(k)) {

                    // Case k = 1:
                    //
                    //   The right inequality is always true, because replacing k by 1 gives
                    //   u >= hIntegral(1.5) - h(1) = hIntegralX1 and u is taken from
                    //   (hIntegralX1, hIntegralNumberOfElements].
                    //
                    //   Therefore, the acceptance rate for k = 1 is P(accepted | k = 1) = 1
                    //   and the probability that 1 is returned as random value is
                    //   P(k = 1 and accepted) = P(accepted | k = 1) * P(k = 1) = C = C / 1^exponent
                    //
                    // Case k >= 2:
                    //
                    //   The left inequality (k - x <= s) is just a short cut
                    //   to avoid the more expensive evaluation of the right inequality
                    //   (u >= hIntegral(k + 0.5) - h(k)) in many cases.
                    //
                    //   If the left inequality is true, the right inequality is also true:
                    //     Theorem 2 in the paper is valid for all positive exponents, because
                    //     the requirements h'(x) = -exponent/x^(exponent + 1) < 0 and
                    //     (-1/hInverse'(x))'' = (1+1/exponent) * x^(1/exponent-1) >= 0
                    //     are both fulfilled.
                    //     Therefore, f(x) := x - hIntegralInverse(hIntegral(x + 0.5) - h(x))
                    //     is a non-decreasing function. If k - x <= s holds,
                    //     k - x <= s + f(k) - f(2) is obviously also true which is equivalent to
                    //     -x <= -hIntegralInverse(hIntegral(k + 0.5) - h(k)),
                    //     -hIntegralInverse(u) <= -hIntegralInverse(hIntegral(k + 0.5) - h(k)),
                    //     and finally u >= hIntegral(k + 0.5) - h(k).
                    //
                    //   Hence, the right inequality determines the acceptance rate:
                    //   P(accepted | k = m) = h(m) / (hIntegrated(m+1/2) - hIntegrated(m-1/2))
                    //   The probability that m is returned is given by
                    //   P(k = m and accepted) = P(accepted | k = m) * P(k = m) = C * h(m) = C / m^exponent.
                    //
                    // In both cases the probabilities are proportional to the probability mass function
                    // of the Zipf distribution.

                    return k;
                }
            }
        }

        /**
         * {@code H(x) :=}
         * <ul>
         * <li>{@code (x^(1-exponent) - 1)/(1 - exponent)}, if {@code exponent != 1}</li>
         * <li>{@code log(x)}, if {@code exponent == 1}</li>
         * </ul>
         * H(x) is an integral function of h(x),
         * the derivative of H(x) is h(x).
         *
         * @param x free parameter
         * @return {@code H(x)}
         */
        private double hIntegral(final double x) {
            final double logX = FastMath.log(x);
            return helper2((1d-exponent)*logX)*logX;
        }

        /**
         * {@code h(x) := 1/x^exponent}
         *
         * @param x free parameter
         * @return h(x)
         */
        private double h(final double x) {
            return FastMath.exp(-exponent * FastMath.log(x));
        }

        /**
         * The inverse function of H(x).
         *
         * @param x free parameter
         * @return y for which {@code H(y) = x}
         */
        private double hIntegralInverse(final double x) {
            double t = x*(1d-exponent);
            if (t < -1d) {
                // Limit value to the range [-1, +inf).
                // t could be smaller than -1 in some rare cases due to numerical errors.
                t = -1;
            }
            return FastMath.exp(helper1(t)*x);
        }

        /**
         * Helper function that calculates {@code log(1+x)/x}.
         * <p>
         * A Taylor series expansion is used, if x is close to 0.
         *
         * @param x a value larger than or equal to -1
         * @return {@code log(1+x)/x}
         */
        static double helper1(final double x) {
            if (FastMath.abs(x)>1e-8) {
                return FastMath.log1p(x)/x;
            }
            else {
                return 1.-x*((1./2.)-x*((1./3.)-x*(1./4.)));
            }
        }

        /**
         * Helper function to calculate {@code (exp(x)-1)/x}.
         * <p>
         * A Taylor series expansion is used, if x is close to 0.
         *
         * @param x free parameter
         * @return {@code (exp(x)-1)/x} if x is non-zero, or 1 if x=0
         */
        static double helper2(final double x) {
            if (FastMath.abs(x)>1e-8) {
                return FastMath.expm1(x)/x;
            }
            else {
                return 1.+x*(1./2.)*(1.+x*(1./3.)*(1.+x*(1./4.)));
            }
        }
    }
}
