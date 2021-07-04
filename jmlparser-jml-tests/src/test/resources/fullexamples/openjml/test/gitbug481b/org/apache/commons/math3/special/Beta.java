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

import org.apache.commons.math3.exception.NumberIsTooSmallException;
import org.apache.commons.math3.exception.OutOfRangeException;
import org.apache.commons.math3.util.ContinuedFraction;
import org.apache.commons.math3.util.FastMath;

/**
 * <p>
 * This is a utility class that provides computation methods related to the
 * Beta family of functions.
 * </p>
 * <p>
 * Implementation of {@link #logBeta(double, double)} is based on the
 * algorithms described in
 * <ul>
 * <li><a href="http://dx.doi.org/10.1145/22721.23109">Didonato and Morris
 *     (1986)</a>, <em>Computation of the Incomplete Gamma Function Ratios
 *     and their Inverse</em>, TOMS 12(4), 377-393,</li>
 * <li><a href="http://dx.doi.org/10.1145/131766.131776">Didonato and Morris
 *     (1992)</a>, <em>Algorithm 708: Significant Digit Computation of the
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
 *
 */
public class Beta {
    /** Maximum allowed numerical error. */
    private static final double DEFAULT_EPSILON = 1E-14;

    /** The constant value of ½log 2π. */
    private static final double HALF_LOG_TWO_PI = .9189385332046727;

    /**
     * <p>
     * The coefficients of the series expansion of the Δ function. This function
     * is defined as follows
     * </p>
     * <center>Δ(x) = log Γ(x) - (x - 0.5) log a + a - 0.5 log 2π,</center>
     * <p>
     * see equation (23) in Didonato and Morris (1992). The series expansion,
     * which applies for x ≥ 10, reads
     * </p>
     * <pre>
     *                 14
     *                ====
     *             1  \                2 n
     *     Δ(x) = ---  >    d  (10 / x)
     *             x  /      n
     *                ====
     *                n = 0
     * <pre>
     */
    private static final double[] DELTA = {
        .833333333333333333333333333333E-01,
        -.277777777777777777777777752282E-04,
        .793650793650793650791732130419E-07,
        -.595238095238095232389839236182E-09,
        .841750841750832853294451671990E-11,
        -.191752691751854612334149171243E-12,
        .641025640510325475730918472625E-14,
        -.295506514125338232839867823991E-15,
        .179643716359402238723287696452E-16,
        -.139228964661627791231203060395E-17,
        .133802855014020915603275339093E-18,
        -.154246009867966094273710216533E-19,
        .197701992980957427278370133333E-20,
        -.234065664793997056856992426667E-21,
        .171348014966398575409015466667E-22
    };

    /**
     * Default constructor.  Prohibit instantiation.
     */
    private Beta() {}

    /**
     * Returns the
     * <a href="http://mathworld.wolfram.com/RegularizedBetaFunction.html">
     * regularized beta function</a> I(x, a, b).
     *
     * @param x Value.
     * @param a Parameter {@code a}.
     * @param b Parameter {@code b}.
     * @return the regularized beta function I(x, a, b).
     * @throws org.apache.commons.math3.exception.MaxCountExceededException
     * if the algorithm fails to converge.
     */
    public static double regularizedBeta(double x, double a, double b) {
        return regularizedBeta(x, a, b, DEFAULT_EPSILON, Integer.MAX_VALUE);
    }

    /**
     * Returns the
     * <a href="http://mathworld.wolfram.com/RegularizedBetaFunction.html">
     * regularized beta function</a> I(x, a, b).
     *
     * @param x Value.
     * @param a Parameter {@code a}.
     * @param b Parameter {@code b}.
     * @param epsilon When the absolute value of the nth item in the
     * series is less than epsilon the approximation ceases to calculate
     * further elements in the series.
     * @return the regularized beta function I(x, a, b)
     * @throws org.apache.commons.math3.exception.MaxCountExceededException
     * if the algorithm fails to converge.
     */
    public static double regularizedBeta(double x,
                                         double a, double b,
                                         double epsilon) {
        return regularizedBeta(x, a, b, epsilon, Integer.MAX_VALUE);
    }

    /**
     * Returns the regularized beta function I(x, a, b).
     *
     * @param x the value.
     * @param a Parameter {@code a}.
     * @param b Parameter {@code b}.
     * @param maxIterations Maximum number of "iterations" to complete.
     * @return the regularized beta function I(x, a, b)
     * @throws org.apache.commons.math3.exception.MaxCountExceededException
     * if the algorithm fails to converge.
     */
    public static double regularizedBeta(double x,
                                         double a, double b,
                                         int maxIterations) {
        return regularizedBeta(x, a, b, DEFAULT_EPSILON, maxIterations);
    }

    /**
     * Returns the regularized beta function I(x, a, b).
     *
     * The implementation of this method is based on:
     * <ul>
     * <li>
     * <a href="http://mathworld.wolfram.com/RegularizedBetaFunction.html">
     * Regularized Beta Function</a>.</li>
     * <li>
     * <a href="http://functions.wolfram.com/06.21.10.0001.01">
     * Regularized Beta Function</a>.</li>
     * </ul>
     *
     * @param x the value.
     * @param a Parameter {@code a}.
     * @param b Parameter {@code b}.
     * @param epsilon When the absolute value of the nth item in the
     * series is less than epsilon the approximation ceases to calculate
     * further elements in the series.
     * @param maxIterations Maximum number of "iterations" to complete.
     * @return the regularized beta function I(x, a, b)
     * @throws org.apache.commons.math3.exception.MaxCountExceededException
     * if the algorithm fails to converge.
     */
    public static double regularizedBeta(double x,
                                         final double a, final double b,
                                         double epsilon, int maxIterations) {
        double ret;

        if (Double.isNaN(x) ||
            Double.isNaN(a) ||
            Double.isNaN(b) ||
            x < 0 ||
            x > 1 ||
            a <= 0 ||
            b <= 0) {
            ret = Double.NaN;
        } else if (x > (a + 1) / (2 + b + a) &&
                   1 - x <= (b + 1) / (2 + b + a)) {
            ret = 1 - regularizedBeta(1 - x, b, a, epsilon, maxIterations);
        } else {
            ContinuedFraction fraction = new ContinuedFraction() {

                /** {@inheritDoc} */
                @Override
                protected double getB(int n, double x) {
                    double ret;
                    double m;
                    if (n % 2 == 0) { // even
                        m = n / 2.0;
                        ret = (m * (b - m) * x) /
                            ((a + (2 * m) - 1) * (a + (2 * m)));
                    } else {
                        m = (n - 1.0) / 2.0;
                        ret = -((a + m) * (a + b + m) * x) /
                                ((a + (2 * m)) * (a + (2 * m) + 1.0));
                    }
                    return ret;
                }

                /** {@inheritDoc} */
                @Override
                protected double getA(int n, double x) {
                    return 1.0;
                }
            };
            ret = FastMath.exp((a * FastMath.log(x)) + (b * FastMath.log1p(-x)) -
                FastMath.log(a) - logBeta(a, b)) *
                1.0 / fraction.evaluate(x, epsilon, maxIterations);
        }

        return ret;
    }

    /**
     * Returns the natural logarithm of the beta function B(a, b).
     *
     * The implementation of this method is based on:
     * <ul>
     * <li><a href="http://mathworld.wolfram.com/BetaFunction.html">
     * Beta Function</a>, equation (1).</li>
     * </ul>
     *
     * @param a Parameter {@code a}.
     * @param b Parameter {@code b}.
     * @param epsilon This parameter is ignored.
     * @param maxIterations This parameter is ignored.
     * @return log(B(a, b)).
     * @deprecated as of version 3.1, this method is deprecated as the
     * computation of the beta function is no longer iterative; it will be
     * removed in version 4.0. Current implementation of this method
     * internally calls {@link #logBeta(double, double)}.
     */
    @Deprecated
    public static double logBeta(double a, double b,
                                 double epsilon,
                                 int maxIterations) {

        return logBeta(a, b);
    }


    /**
     * Returns the value of log Γ(a + b) for 1 ≤ a, b ≤ 2. Based on the
     * <em>NSWC Library of Mathematics Subroutines</em> double precision
     * implementation, {@code DGSMLN}. In {@code BetaTest.testLogGammaSum()},
     * this private method is accessed through reflection.
     *
     * @param a First argument.
     * @param b Second argument.
     * @return the value of {@code log(Gamma(a + b))}.
     * @throws OutOfRangeException if {@code a} or {@code b} is lower than
     * {@code 1.0} or greater than {@code 2.0}.
     */
    private static double logGammaSum(final double a, final double b)
        throws OutOfRangeException {

        if ((a < 1.0) || (a > 2.0)) {
            throw new OutOfRangeException(a, 1.0, 2.0);
        }
        if ((b < 1.0) || (b > 2.0)) {
            throw new OutOfRangeException(b, 1.0, 2.0);
        }

        final double x = (a - 1.0) + (b - 1.0);
        if (x <= 0.5) {
            return Gamma.logGamma1p(1.0 + x);
        } else if (x <= 1.5) {
            return Gamma.logGamma1p(x) + FastMath.log1p(x);
        } else {
            return Gamma.logGamma1p(x - 1.0) + FastMath.log(x * (1.0 + x));
        }
    }

    /**
     * Returns the value of log[Γ(b) / Γ(a + b)] for a ≥ 0 and b ≥ 10. Based on
     * the <em>NSWC Library of Mathematics Subroutines</em> double precision
     * implementation, {@code DLGDIV}. In
     * {@code BetaTest.testLogGammaMinusLogGammaSum()}, this private method is
     * accessed through reflection.
     *
     * @param a First argument.
     * @param b Second argument.
     * @return the value of {@code log(Gamma(b) / Gamma(a + b))}.
     * @throws NumberIsTooSmallException if {@code a < 0.0} or {@code b < 10.0}.
     */
    private static double logGammaMinusLogGammaSum(final double a,
                                                   final double b)
        throws NumberIsTooSmallException {

        if (a < 0.0) {
            throw new NumberIsTooSmallException(a, 0.0, true);
        }
        if (b < 10.0) {
            throw new NumberIsTooSmallException(b, 10.0, true);
        }

        /*
         * d = a + b - 0.5
         */
        final double d;
        final double w;
        if (a <= b) {
            d = b + (a - 0.5);
            w = deltaMinusDeltaSum(a, b);
        } else {
            d = a + (b - 0.5);
            w = deltaMinusDeltaSum(b, a);
        }

        final double u = d * FastMath.log1p(a / b);
        final double v = a * (FastMath.log(b) - 1.0);

        return u <= v ? (w - u) - v : (w - v) - u;
    }

    /**
     * Returns the value of Δ(b) - Δ(a + b), with 0 ≤ a ≤ b and b ≥ 10. Based
     * on equations (26), (27) and (28) in Didonato and Morris (1992).
     *
     * @param a First argument.
     * @param b Second argument.
     * @return the value of {@code Delta(b) - Delta(a + b)}
     * @throws OutOfRangeException if {@code a < 0} or {@code a > b}
     * @throws NumberIsTooSmallException if {@code b < 10}
     */
    private static double deltaMinusDeltaSum(final double a,
                                             final double b)
        throws OutOfRangeException, NumberIsTooSmallException {

        if ((a < 0) || (a > b)) {
            throw new OutOfRangeException(a, 0, b);
        }
        if (b < 10) {
            throw new NumberIsTooSmallException(b, 10, true);
        }

        final double h = a / b;
        final double p = h / (1.0 + h);
        final double q = 1.0 / (1.0 + h);
        final double q2 = q * q;
        /*
         * s[i] = 1 + q + ... - q**(2 * i)
         */
        final double[] s = new double[DELTA.length];
        s[0] = 1.0;
        for (int i = 1; i < s.length; i++) {
            s[i] = 1.0 + (q + q2 * s[i - 1]);
        }
        /*
         * w = Delta(b) - Delta(a + b)
         */
        final double sqrtT = 10.0 / b;
        final double t = sqrtT * sqrtT;
        double w = DELTA[DELTA.length - 1] * s[s.length - 1];
        for (int i = DELTA.length - 2; i >= 0; i--) {
            w = t * w + DELTA[i] * s[i];
        }
        return w * p / b;
    }

    /**
     * Returns the value of Δ(p) + Δ(q) - Δ(p + q), with p, q ≥ 10. Based on
     * the <em>NSWC Library of Mathematics Subroutines</em> double precision
     * implementation, {@code DBCORR}. In
     * {@code BetaTest.testSumDeltaMinusDeltaSum()}, this private method is
     * accessed through reflection.
     *
     * @param p First argument.
     * @param q Second argument.
     * @return the value of {@code Delta(p) + Delta(q) - Delta(p + q)}.
     * @throws NumberIsTooSmallException if {@code p < 10.0} or {@code q < 10.0}.
     */
    private static double sumDeltaMinusDeltaSum(final double p,
                                                final double q) {

        if (p < 10.0) {
            throw new NumberIsTooSmallException(p, 10.0, true);
        }
        if (q < 10.0) {
            throw new NumberIsTooSmallException(q, 10.0, true);
        }

        final double a = FastMath.min(p, q);
        final double b = FastMath.max(p, q);
        final double sqrtT = 10.0 / a;
        final double t = sqrtT * sqrtT;
        double z = DELTA[DELTA.length - 1];
        for (int i = DELTA.length - 2; i >= 0; i--) {
            z = t * z + DELTA[i];
        }
        return z / a + deltaMinusDeltaSum(a, b);
    }

    /**
     * Returns the value of log B(p, q) for 0 ≤ x ≤ 1 and p, q > 0. Based on the
     * <em>NSWC Library of Mathematics Subroutines</em> implementation,
     * {@code DBETLN}.
     *
     * @param p First argument.
     * @param q Second argument.
     * @return the value of {@code log(Beta(p, q))}, {@code NaN} if
     * {@code p <= 0} or {@code q <= 0}.
     */
    public static double logBeta(final double p, final double q) {
        if (Double.isNaN(p) || Double.isNaN(q) || (p <= 0.0) || (q <= 0.0)) {
            return Double.NaN;
        }

        final double a = FastMath.min(p, q);
        final double b = FastMath.max(p, q);
        if (a >= 10.0) {
            final double w = sumDeltaMinusDeltaSum(a, b);
            final double h = a / b;
            final double c = h / (1.0 + h);
            final double u = -(a - 0.5) * FastMath.log(c);
            final double v = b * FastMath.log1p(h);
            if (u <= v) {
                return (((-0.5 * FastMath.log(b) + HALF_LOG_TWO_PI) + w) - u) - v;
            } else {
                return (((-0.5 * FastMath.log(b) + HALF_LOG_TWO_PI) + w) - v) - u;
            }
        } else if (a > 2.0) {
            if (b > 1000.0) {
                final int n = (int) FastMath.floor(a - 1.0);
                double prod = 1.0;
                double ared = a;
                for (int i = 0; i < n; i++) {
                    ared -= 1.0;
                    prod *= ared / (1.0 + ared / b);
                }
                return (FastMath.log(prod) - n * FastMath.log(b)) +
                        (Gamma.logGamma(ared) +
                         logGammaMinusLogGammaSum(ared, b));
            } else {
                double prod1 = 1.0;
                double ared = a;
                while (ared > 2.0) {
                    ared -= 1.0;
                    final double h = ared / b;
                    prod1 *= h / (1.0 + h);
                }
                if (b < 10.0) {
                    double prod2 = 1.0;
                    double bred = b;
                    while (bred > 2.0) {
                        bred -= 1.0;
                        prod2 *= bred / (ared + bred);
                    }
                    return FastMath.log(prod1) +
                           FastMath.log(prod2) +
                           (Gamma.logGamma(ared) +
                           (Gamma.logGamma(bred) -
                            logGammaSum(ared, bred)));
                } else {
                    return FastMath.log(prod1) +
                           Gamma.logGamma(ared) +
                           logGammaMinusLogGammaSum(ared, b);
                }
            }
        } else if (a >= 1.0) {
            if (b > 2.0) {
                if (b < 10.0) {
                    double prod = 1.0;
                    double bred = b;
                    while (bred > 2.0) {
                        bred -= 1.0;
                        prod *= bred / (a + bred);
                    }
                    return FastMath.log(prod) +
                           (Gamma.logGamma(a) +
                            (Gamma.logGamma(bred) -
                             logGammaSum(a, bred)));
                } else {
                    return Gamma.logGamma(a) +
                           logGammaMinusLogGammaSum(a, b);
                }
            } else {
                return Gamma.logGamma(a) +
                       Gamma.logGamma(b) -
                       logGammaSum(a, b);
            }
        } else {
            if (b >= 10.0) {
                return Gamma.logGamma(a) +
                       logGammaMinusLogGammaSum(a, b);
            } else {
                // The following command is the original NSWC implementation.
                // return Gamma.logGamma(a) +
                // (Gamma.logGamma(b) - Gamma.logGamma(a + b));
                // The following command turns out to be more accurate.
                return FastMath.log(Gamma.gamma(a) * Gamma.gamma(b) /
                                    Gamma.gamma(a + b));
            }
        }
    }
}
