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
package org.apache.commons.math3.special;

import org.apache.commons.math3.exception.MaxCountExceededException;
import org.apache.commons.math3.exception.NumberIsTooLargeException;
import org.apache.commons.math3.exception.NumberIsTooSmallException;
import org.apache.commons.math3.util.ContinuedFraction;
import org.apache.commons.math3.util.FastMath;

/**
 * <p>
 * This is a utility class that provides computation methods related to the
 * &Gamma; (Gamma) family of functions.
 * </p>
 * <p>
 * Implementation of {@link #invGamma1pm1(double)} and
 * {@link #logGamma1p(double)} is based on the algorithms described in
 * <ul>
 * <li><a href="http://dx.doi.org/10.1145/22721.23109">Didonato and Morris
 * (1986)</a>, <em>Computation of the Incomplete Gamma Function Ratios and
 *     their Inverse</em>, TOMS 12(4), 377-393,</li>
 * <li><a href="http://dx.doi.org/10.1145/131766.131776">Didonato and Morris
 * (1992)</a>, <em>Algorithm 708: Significant Digit Computation of the
 *     Incomplete Beta Function Ratios</em>, TOMS 18(3), 360-373,</li>
 * </ul>
 * and implemented in the
 * <a href="http://www.dtic.mil/docs/citations/ADA476840">NSWC Library of Mathematical Functions</a>,
 * available
 * <a href="http://www.ualberta.ca/CNS/RESEARCH/Software/NumericalNSWC/site.html">here</a>.
 * This library is "approved for public release", and the
 * <a href="http://www.dtic.mil/dtic/pdf/announcements/CopyrightGuidance.pdf">Copyright guidance</a>
 * indicates that unless otherwise stated in the code, all FORTRAN functions in
 * this library are license free. Since no such notice appears in the code these
 * functions can safely be ported to Commons-Math.
 * </p>
 *
 */
public class Gamma {
    /**
     * <a href="http://en.wikipedia.org/wiki/Euler-Mascheroni_constant">Euler-Mascheroni constant</a>
     * @since 2.0
     */
    public static final double GAMMA = 0.577215664901532860606512090082;

    /**
     * The value of the {@code g} constant in the Lanczos approximation, see
     * {@link #lanczos(double)}.
     * @since 3.1
     */
    public static final double LANCZOS_G = 607.0 / 128.0;

    /** Maximum allowed numerical error. */
    private static final double DEFAULT_EPSILON = 10e-15;

    /** Lanczos coefficients */
    private static final double[] LANCZOS = {
        0.99999999999999709182,
        57.156235665862923517,
        -59.597960355475491248,
        14.136097974741747174,
        -0.49191381609762019978,
        .33994649984811888699e-4,
        .46523628927048575665e-4,
        -.98374475304879564677e-4,
        .15808870322491248884e-3,
        -.21026444172410488319e-3,
        .21743961811521264320e-3,
        -.16431810653676389022e-3,
        .84418223983852743293e-4,
        -.26190838401581408670e-4,
        .36899182659531622704e-5,
    };

    /** Avoid repeated computation of log of 2 PI in logGamma */
    private static final double HALF_LOG_2_PI = 0.5 * FastMath.log(2.0 * FastMath.PI);

    /** The constant value of &radic;(2&pi;). */
    private static final double SQRT_TWO_PI = 2.506628274631000502;

    // limits for switching algorithm in digamma
    /** C limit. */
    private static final double C_LIMIT = 49;

    /** S limit. */
    private static final double S_LIMIT = 1e-5;

    /*
     * Constants for the computation of double invGamma1pm1(double).
     * Copied from DGAM1 in the NSWC library.
     */

    /** The constant {@code A0} defined in {@code DGAM1}. */
    private static final double INV_GAMMA1P_M1_A0 = .611609510448141581788E-08;

    /** The constant {@code A1} defined in {@code DGAM1}. */
    private static final double INV_GAMMA1P_M1_A1 = .624730830116465516210E-08;

    /** The constant {@code B1} defined in {@code DGAM1}. */
    private static final double INV_GAMMA1P_M1_B1 = .203610414066806987300E+00;

    /** The constant {@code B2} defined in {@code DGAM1}. */
    private static final double INV_GAMMA1P_M1_B2 = .266205348428949217746E-01;

    /** The constant {@code B3} defined in {@code DGAM1}. */
    private static final double INV_GAMMA1P_M1_B3 = .493944979382446875238E-03;

    /** The constant {@code B4} defined in {@code DGAM1}. */
    private static final double INV_GAMMA1P_M1_B4 = -.851419432440314906588E-05;

    /** The constant {@code B5} defined in {@code DGAM1}. */
    private static final double INV_GAMMA1P_M1_B5 = -.643045481779353022248E-05;

    /** The constant {@code B6} defined in {@code DGAM1}. */
    private static final double INV_GAMMA1P_M1_B6 = .992641840672773722196E-06;

    /** The constant {@code B7} defined in {@code DGAM1}. */
    private static final double INV_GAMMA1P_M1_B7 = -.607761895722825260739E-07;

    /** The constant {@code B8} defined in {@code DGAM1}. */
    private static final double INV_GAMMA1P_M1_B8 = .195755836614639731882E-09;

    /** The constant {@code P0} defined in {@code DGAM1}. */
    private static final double INV_GAMMA1P_M1_P0 = .6116095104481415817861E-08;

    /** The constant {@code P1} defined in {@code DGAM1}. */
    private static final double INV_GAMMA1P_M1_P1 = .6871674113067198736152E-08;

    /** The constant {@code P2} defined in {@code DGAM1}. */
    private static final double INV_GAMMA1P_M1_P2 = .6820161668496170657918E-09;

    /** The constant {@code P3} defined in {@code DGAM1}. */
    private static final double INV_GAMMA1P_M1_P3 = .4686843322948848031080E-10;

    /** The constant {@code P4} defined in {@code DGAM1}. */
    private static final double INV_GAMMA1P_M1_P4 = .1572833027710446286995E-11;

    /** The constant {@code P5} defined in {@code DGAM1}. */
    private static final double INV_GAMMA1P_M1_P5 = -.1249441572276366213222E-12;

    /** The constant {@code P6} defined in {@code DGAM1}. */
    private static final double INV_GAMMA1P_M1_P6 = .4343529937408594255178E-14;

    /** The constant {@code Q1} defined in {@code DGAM1}. */
    private static final double INV_GAMMA1P_M1_Q1 = .3056961078365221025009E+00;

    /** The constant {@code Q2} defined in {@code DGAM1}. */
    private static final double INV_GAMMA1P_M1_Q2 = .5464213086042296536016E-01;

    /** The constant {@code Q3} defined in {@code DGAM1}. */
    private static final double INV_GAMMA1P_M1_Q3 = .4956830093825887312020E-02;

    /** The constant {@code Q4} defined in {@code DGAM1}. */
    private static final double INV_GAMMA1P_M1_Q4 = .2692369466186361192876E-03;

    /** The constant {@code C} defined in {@code DGAM1}. */
    private static final double INV_GAMMA1P_M1_C = -.422784335098467139393487909917598E+00;

    /** The constant {@code C0} defined in {@code DGAM1}. */
    private static final double INV_GAMMA1P_M1_C0 = .577215664901532860606512090082402E+00;

    /** The constant {@code C1} defined in {@code DGAM1}. */
    private static final double INV_GAMMA1P_M1_C1 = -.655878071520253881077019515145390E+00;

    /** The constant {@code C2} defined in {@code DGAM1}. */
    private static final double INV_GAMMA1P_M1_C2 = -.420026350340952355290039348754298E-01;

    /** The constant {@code C3} defined in {@code DGAM1}. */
    private static final double INV_GAMMA1P_M1_C3 = .166538611382291489501700795102105E+00;

    /** The constant {@code C4} defined in {@code DGAM1}. */
    private static final double INV_GAMMA1P_M1_C4 = -.421977345555443367482083012891874E-01;

    /** The constant {@code C5} defined in {@code DGAM1}. */
    private static final double INV_GAMMA1P_M1_C5 = -.962197152787697356211492167234820E-02;

    /** The constant {@code C6} defined in {@code DGAM1}. */
    private static final double INV_GAMMA1P_M1_C6 = .721894324666309954239501034044657E-02;

    /** The constant {@code C7} defined in {@code DGAM1}. */
    private static final double INV_GAMMA1P_M1_C7 = -.116516759185906511211397108401839E-02;

    /** The constant {@code C8} defined in {@code DGAM1}. */
    private static final double INV_GAMMA1P_M1_C8 = -.215241674114950972815729963053648E-03;

    /** The constant {@code C9} defined in {@code DGAM1}. */
    private static final double INV_GAMMA1P_M1_C9 = .128050282388116186153198626328164E-03;

    /** The constant {@code C10} defined in {@code DGAM1}. */
    private static final double INV_GAMMA1P_M1_C10 = -.201348547807882386556893914210218E-04;

    /** The constant {@code C11} defined in {@code DGAM1}. */
    private static final double INV_GAMMA1P_M1_C11 = -.125049348214267065734535947383309E-05;

    /** The constant {@code C12} defined in {@code DGAM1}. */
    private static final double INV_GAMMA1P_M1_C12 = .113302723198169588237412962033074E-05;

    /** The constant {@code C13} defined in {@code DGAM1}. */
    private static final double INV_GAMMA1P_M1_C13 = -.205633841697760710345015413002057E-06;

    /**
     * Default constructor.  Prohibit instantiation.
     */
    private Gamma() {}

    /**
     * <p>
     * Returns the value of log&nbsp;&Gamma;(x) for x&nbsp;&gt;&nbsp;0.
     * </p>
     * <p>
     * For x &le; 8, the implementation is based on the double precision
     * implementation in the <em>NSWC Library of Mathematics Subroutines</em>,
     * {@code DGAMLN}. For x &gt; 8, the implementation is based on
     * </p>
     * <ul>
     * <li><a href="http://mathworld.wolfram.com/GammaFunction.html">Gamma
     *     Function</a>, equation (28).</li>
     * <li><a href="http://mathworld.wolfram.com/LanczosApproximation.html">
     *     Lanczos Approximation</a>, equations (1) through (5).</li>
     * <li><a href="http://my.fit.edu/~gabdo/gamma.txt">Paul Godfrey, A note on
     *     the computation of the convergent Lanczos complex Gamma
     *     approximation</a></li>
     * </ul>
     *
     * @param x Argument.
     * @return the value of {@code log(Gamma(x))}, {@code Double.NaN} if
     * {@code x <= 0.0}.
     */
    public static double logGamma(double x) {
        double ret;

        if (Double.isNaN(x) || (x <= 0.0)) {
            ret = Double.NaN;
        } else if (x < 0.5) {
            return logGamma1p(x) - FastMath.log(x);
        } else if (x <= 2.5) {
            return logGamma1p((x - 0.5) - 0.5);
        } else if (x <= 8.0) {
            final int n = (int) FastMath.floor(x - 1.5);
            double prod = 1.0;
            for (int i = 1; i <= n; i++) {
                prod *= x - i;
            }
            return logGamma1p(x - (n + 1)) + FastMath.log(prod);
        } else {
            double sum = lanczos(x);
            double tmp = x + LANCZOS_G + .5;
            ret = ((x + .5) * FastMath.log(tmp)) - tmp +
                HALF_LOG_2_PI + FastMath.log(sum / x);
        }

        return ret;
    }

    /**
     * Returns the regularized gamma function P(a, x).
     *
     * @param a Parameter.
     * @param x Value.
     * @return the regularized gamma function P(a, x).
     * @throws MaxCountExceededException if the algorithm fails to converge.
     */
    public static double regularizedGammaP(double a, double x) {
        return regularizedGammaP(a, x, DEFAULT_EPSILON, Integer.MAX_VALUE);
    }

    /**
     * Returns the regularized gamma function P(a, x).
     *
     * The implementation of this method is based on:
     * <ul>
     *  <li>
     *   <a href="http://mathworld.wolfram.com/RegularizedGammaFunction.html">
     *   Regularized Gamma Function</a>, equation (1)
     *  </li>
     *  <li>
     *   <a href="http://mathworld.wolfram.com/IncompleteGammaFunction.html">
     *   Incomplete Gamma Function</a>, equation (4).
     *  </li>
     *  <li>
     *   <a href="http://mathworld.wolfram.com/ConfluentHypergeometricFunctionoftheFirstKind.html">
     *   Confluent Hypergeometric Function of the First Kind</a>, equation (1).
     *  </li>
     * </ul>
     *
     * @param a the a parameter.
     * @param x the value.
     * @param epsilon When the absolute value of the nth item in the
     * series is less than epsilon the approximation ceases to calculate
     * further elements in the series.
     * @param maxIterations Maximum number of "iterations" to complete.
     * @return the regularized gamma function P(a, x)
     * @throws MaxCountExceededException if the algorithm fails to converge.
     */
    public static double regularizedGammaP(double a,
                                           double x,
                                           double epsilon,
                                           int maxIterations) {
        double ret;

        if (Double.isNaN(a) || Double.isNaN(x) || (a <= 0.0) || (x < 0.0)) {
            ret = Double.NaN;
        } else if (x == 0.0) {
            ret = 0.0;
        } else if (x >= a + 1) {
            // use regularizedGammaQ because it should converge faster in this
            // case.
            ret = 1.0 - regularizedGammaQ(a, x, epsilon, maxIterations);
        } else {
            // calculate series
            double n = 0.0; // current element index
            double an = 1.0 / a; // n-th element in the series
            double sum = an; // partial sum
            while (FastMath.abs(an/sum) > epsilon &&
                   n < maxIterations &&
                   sum < Double.POSITIVE_INFINITY) {
                // compute next element in the series
                n += 1.0;
                an *= x / (a + n);

                // update partial sum
                sum += an;
            }
            if (n >= maxIterations) {
                throw new MaxCountExceededException(maxIterations);
            } else if (Double.isInfinite(sum)) {
                ret = 1.0;
            } else {
                ret = FastMath.exp(-x + (a * FastMath.log(x)) - logGamma(a)) * sum;
            }
        }

        return ret;
    }

    /**
     * Returns the regularized gamma function Q(a, x) = 1 - P(a, x).
     *
     * @param a the a parameter.
     * @param x the value.
     * @return the regularized gamma function Q(a, x)
     * @throws MaxCountExceededException if the algorithm fails to converge.
     */
    public static double regularizedGammaQ(double a, double x) {
        return regularizedGammaQ(a, x, DEFAULT_EPSILON, Integer.MAX_VALUE);
    }

    /**
     * Returns the regularized gamma function Q(a, x) = 1 - P(a, x).
     *
     * The implementation of this method is based on:
     * <ul>
     *  <li>
     *   <a href="http://mathworld.wolfram.com/RegularizedGammaFunction.html">
     *   Regularized Gamma Function</a>, equation (1).
     *  </li>
     *  <li>
     *   <a href="http://functions.wolfram.com/GammaBetaErf/GammaRegularized/10/0003/">
     *   Regularized incomplete gamma function: Continued fraction representations
     *   (formula 06.08.10.0003)</a>
     *  </li>
     * </ul>
     *
     * @param a the a parameter.
     * @param x the value.
     * @param epsilon When the absolute value of the nth item in the
     * series is less than epsilon the approximation ceases to calculate
     * further elements in the series.
     * @param maxIterations Maximum number of "iterations" to complete.
     * @return the regularized gamma function P(a, x)
     * @throws MaxCountExceededException if the algorithm fails to converge.
     */
    public static double regularizedGammaQ(final double a,
                                           double x,
                                           double epsilon,
                                           int maxIterations) {
        double ret;

        if (Double.isNaN(a) || Double.isNaN(x) || (a <= 0.0) || (x < 0.0)) {
            ret = Double.NaN;
        } else if (x == 0.0) {
            ret = 1.0;
        } else if (x < a + 1.0) {
            // use regularizedGammaP because it should converge faster in this
            // case.
            ret = 1.0 - regularizedGammaP(a, x, epsilon, maxIterations);
        } else {
            // create continued fraction
            ContinuedFraction cf = new ContinuedFraction() {

                /** {@inheritDoc} */
                @Override
                protected double getA(int n, double x) {
                    return ((2.0 * n) + 1.0) - a + x;
                }

                /** {@inheritDoc} */
                @Override
                protected double getB(int n, double x) {
                    return n * (a - n);
                }
            };

            ret = 1.0 / cf.evaluate(x, epsilon, maxIterations);
            ret = FastMath.exp(-x + (a * FastMath.log(x)) - logGamma(a)) * ret;
        }

        return ret;
    }


    /**
     * <p>Computes the digamma function of x.</p>
     *
     * <p>This is an independently written implementation of the algorithm described in
     * Jose Bernardo, Algorithm AS 103: Psi (Digamma) Function, Applied Statistics, 1976.</p>
     *
     * <p>Some of the constants have been changed to increase accuracy at the moderate expense
     * of run-time.  The result should be accurate to within 10^-8 absolute tolerance for
     * x >= 10^-5 and within 10^-8 relative tolerance for x > 0.</p>
     *
     * <p>Performance for large negative values of x will be quite expensive (proportional to
     * |x|).  Accuracy for negative values of x should be about 10^-8 absolute for results
     * less than 10^5 and 10^-8 relative for results larger than that.</p>
     *
     * @param x Argument.
     * @return digamma(x) to within 10-8 relative or absolute error whichever is smaller.
     * @see <a href="http://en.wikipedia.org/wiki/Digamma_function">Digamma</a>
     * @see <a href="http://www.uv.es/~bernardo/1976AppStatist.pdf">Bernardo&apos;s original article </a>
     * @since 2.0
     */
    public static double digamma(double x) {
        if (Double.isNaN(x) || Double.isInfinite(x)) {
            return x;
        }

        if (x > 0 && x <= S_LIMIT) {
            // use method 5 from Bernardo AS103
            // accurate to O(x)
            return -GAMMA - 1 / x;
        }

        if (x >= C_LIMIT) {
            // use method 4 (accurate to O(1/x^8)
            double inv = 1 / (x * x);
            //            1       1        1         1
            // log(x) -  --- - ------ + ------- - -------
            //           2 x   12 x^2   120 x^4   252 x^6
            return FastMath.log(x) - 0.5 / x - inv * ((1.0 / 12) + inv * (1.0 / 120 - inv / 252));
        }

        return digamma(x + 1) - 1 / x;
    }

    /**
     * Computes the trigamma function of x.
     * This function is derived by taking the derivative of the implementation
     * of digamma.
     *
     * @param x Argument.
     * @return trigamma(x) to within 10-8 relative or absolute error whichever is smaller
     * @see <a href="http://en.wikipedia.org/wiki/Trigamma_function">Trigamma</a>
     * @see Gamma#digamma(double)
     * @since 2.0
     */
    public static double trigamma(double x) {
        if (Double.isNaN(x) || Double.isInfinite(x)) {
            return x;
        }

        if (x > 0 && x <= S_LIMIT) {
            return 1 / (x * x);
        }

        if (x >= C_LIMIT) {
            double inv = 1 / (x * x);
            //  1    1      1       1       1
            //  - + ---- + ---- - ----- + -----
            //  x      2      3       5       7
            //      2 x    6 x    30 x    42 x
            return 1 / x + inv / 2 + inv / x * (1.0 / 6 - inv * (1.0 / 30 + inv / 42));
        }

        return trigamma(x + 1) + 1 / (x * x);
    }

    /**
     * <p>
     * Returns the Lanczos approximation used to compute the gamma function.
     * The Lanczos approximation is related to the Gamma function by the
     * following equation
     * <center>
     * {@code gamma(x) = sqrt(2 * pi) / x * (x + g + 0.5) ^ (x + 0.5)
     *                   * exp(-x - g - 0.5) * lanczos(x)},
     * </center>
     * where {@code g} is the Lanczos constant.
     * </p>
     *
     * @param x Argument.
     * @return The Lanczos approximation.
     * @see <a href="http://mathworld.wolfram.com/LanczosApproximation.html">Lanczos Approximation</a>
     * equations (1) through (5), and Paul Godfrey's
     * <a href="http://my.fit.edu/~gabdo/gamma.txt">Note on the computation
     * of the convergent Lanczos complex Gamma approximation</a>
     * @since 3.1
     */
    public static double lanczos(final double x) {
        double sum = 0.0;
        for (int i = LANCZOS.length - 1; i > 0; --i) {
            sum += LANCZOS[i] / (x + i);
        }
        return sum + LANCZOS[0];
    }

    /**
     * Returns the value of 1 / &Gamma;(1 + x) - 1 for -0&#46;5 &le; x &le;
     * 1&#46;5. This implementation is based on the double precision
     * implementation in the <em>NSWC Library of Mathematics Subroutines</em>,
     * {@code DGAM1}.
     *
     * @param x Argument.
     * @return The value of {@code 1.0 / Gamma(1.0 + x) - 1.0}.
     * @throws NumberIsTooSmallException if {@code x < -0.5}
     * @throws NumberIsTooLargeException if {@code x > 1.5}
     * @since 3.1
     */
    public static double invGamma1pm1(final double x) {

        if (x < -0.5) {
            throw new NumberIsTooSmallException(x, -0.5, true);
        }
        if (x > 1.5) {
            throw new NumberIsTooLargeException(x, 1.5, true);
        }

        final double ret;
        final double t = x <= 0.5 ? x : (x - 0.5) - 0.5;
        if (t < 0.0) {
            final double a = INV_GAMMA1P_M1_A0 + t * INV_GAMMA1P_M1_A1;
            double b = INV_GAMMA1P_M1_B8;
            b = INV_GAMMA1P_M1_B7 + t * b;
            b = INV_GAMMA1P_M1_B6 + t * b;
            b = INV_GAMMA1P_M1_B5 + t * b;
            b = INV_GAMMA1P_M1_B4 + t * b;
            b = INV_GAMMA1P_M1_B3 + t * b;
            b = INV_GAMMA1P_M1_B2 + t * b;
            b = INV_GAMMA1P_M1_B1 + t * b;
            b = 1.0 + t * b;

            double c = INV_GAMMA1P_M1_C13 + t * (a / b);
            c = INV_GAMMA1P_M1_C12 + t * c;
            c = INV_GAMMA1P_M1_C11 + t * c;
            c = INV_GAMMA1P_M1_C10 + t * c;
            c = INV_GAMMA1P_M1_C9 + t * c;
            c = INV_GAMMA1P_M1_C8 + t * c;
            c = INV_GAMMA1P_M1_C7 + t * c;
            c = INV_GAMMA1P_M1_C6 + t * c;
            c = INV_GAMMA1P_M1_C5 + t * c;
            c = INV_GAMMA1P_M1_C4 + t * c;
            c = INV_GAMMA1P_M1_C3 + t * c;
            c = INV_GAMMA1P_M1_C2 + t * c;
            c = INV_GAMMA1P_M1_C1 + t * c;
            c = INV_GAMMA1P_M1_C + t * c;
            if (x > 0.5) {
                ret = t * c / x;
            } else {
                ret = x * ((c + 0.5) + 0.5);
            }
        } else {
            double p = INV_GAMMA1P_M1_P6;
            p = INV_GAMMA1P_M1_P5 + t * p;
            p = INV_GAMMA1P_M1_P4 + t * p;
            p = INV_GAMMA1P_M1_P3 + t * p;
            p = INV_GAMMA1P_M1_P2 + t * p;
            p = INV_GAMMA1P_M1_P1 + t * p;
            p = INV_GAMMA1P_M1_P0 + t * p;

            double q = INV_GAMMA1P_M1_Q4;
            q = INV_GAMMA1P_M1_Q3 + t * q;
            q = INV_GAMMA1P_M1_Q2 + t * q;
            q = INV_GAMMA1P_M1_Q1 + t * q;
            q = 1.0 + t * q;

            double c = INV_GAMMA1P_M1_C13 + (p / q) * t;
            c = INV_GAMMA1P_M1_C12 + t * c;
            c = INV_GAMMA1P_M1_C11 + t * c;
            c = INV_GAMMA1P_M1_C10 + t * c;
            c = INV_GAMMA1P_M1_C9 + t * c;
            c = INV_GAMMA1P_M1_C8 + t * c;
            c = INV_GAMMA1P_M1_C7 + t * c;
            c = INV_GAMMA1P_M1_C6 + t * c;
            c = INV_GAMMA1P_M1_C5 + t * c;
            c = INV_GAMMA1P_M1_C4 + t * c;
            c = INV_GAMMA1P_M1_C3 + t * c;
            c = INV_GAMMA1P_M1_C2 + t * c;
            c = INV_GAMMA1P_M1_C1 + t * c;
            c = INV_GAMMA1P_M1_C0 + t * c;

            if (x > 0.5) {
                ret = (t / x) * ((c - 0.5) - 0.5);
            } else {
                ret = x * c;
            }
        }

        return ret;
    }

    /**
     * Returns the value of log &Gamma;(1 + x) for -0&#46;5 &le; x &le; 1&#46;5.
     * This implementation is based on the double precision implementation in
     * the <em>NSWC Library of Mathematics Subroutines</em>, {@code DGMLN1}.
     *
     * @param x Argument.
     * @return The value of {@code log(Gamma(1 + x))}.
     * @throws NumberIsTooSmallException if {@code x < -0.5}.
     * @throws NumberIsTooLargeException if {@code x > 1.5}.
     * @since 3.1
     */
    public static double logGamma1p(final double x)
        throws NumberIsTooSmallException, NumberIsTooLargeException {

        if (x < -0.5) {
            throw new NumberIsTooSmallException(x, -0.5, true);
        }
        if (x > 1.5) {
            throw new NumberIsTooLargeException(x, 1.5, true);
        }

        return -FastMath.log1p(invGamma1pm1(x));
    }


    /**
     * Returns the value of Γ(x). Based on the <em>NSWC Library of
     * Mathematics Subroutines</em> double precision implementation,
     * {@code DGAMMA}.
     *
     * @param x Argument.
     * @return the value of {@code Gamma(x)}.
     * @since 3.1
     */
    public static double gamma(final double x) {

        if ((x == FastMath.rint(x)) && (x <= 0.0)) {
            return Double.NaN;
        }

        final double ret;
        final double absX = FastMath.abs(x);
        if (absX <= 20.0) {
            if (x >= 1.0) {
                /*
                 * From the recurrence relation
                 * Gamma(x) = (x - 1) * ... * (x - n) * Gamma(x - n),
                 * then
                 * Gamma(t) = 1 / [1 + invGamma1pm1(t - 1)],
                 * where t = x - n. This means that t must satisfy
                 * -0.5 <= t - 1 <= 1.5.
                 */
                double prod = 1.0;
                double t = x;
                while (t > 2.5) {
                    t -= 1.0;
                    prod *= t;
                }
                ret = prod / (1.0 + invGamma1pm1(t - 1.0));
            } else {
                /*
                 * From the recurrence relation
                 * Gamma(x) = Gamma(x + n + 1) / [x * (x + 1) * ... * (x + n)]
                 * then
                 * Gamma(x + n + 1) = 1 / [1 + invGamma1pm1(x + n)],
                 * which requires -0.5 <= x + n <= 1.5.
                 */
                double prod = x;
                double t = x;
                while (t < -0.5) {
                    t += 1.0;
                    prod *= t;
                }
                ret = 1.0 / (prod * (1.0 + invGamma1pm1(t)));
            }
        } else {
            final double y = absX + LANCZOS_G + 0.5;
            final double gammaAbs = SQRT_TWO_PI / absX *
                                    FastMath.pow(y, absX + 0.5) *
                                    FastMath.exp(-y) * lanczos(absX);
            if (x > 0.0) {
                ret = gammaAbs;
            } else {
                /*
                 * From the reflection formula
                 * Gamma(x) * Gamma(1 - x) * sin(pi * x) = pi,
                 * and the recurrence relation
                 * Gamma(1 - x) = -x * Gamma(-x),
                 * it is found
                 * Gamma(x) = -pi / [x * sin(pi * x) * Gamma(-x)].
                 */
                ret = -FastMath.PI /
                      (x * FastMath.sin(FastMath.PI * x) * gammaAbs);
            }
        }
        return ret;
    }
}
