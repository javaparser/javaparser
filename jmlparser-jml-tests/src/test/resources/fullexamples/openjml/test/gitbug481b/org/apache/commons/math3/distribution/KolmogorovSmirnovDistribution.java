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

import java.io.Serializable;
import java.math.BigDecimal;

import org.apache.commons.math3.exception.MathArithmeticException;
import org.apache.commons.math3.exception.NotStrictlyPositiveException;
import org.apache.commons.math3.exception.NumberIsTooLargeException;
import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.fraction.BigFraction;
import org.apache.commons.math3.fraction.BigFractionField;
import org.apache.commons.math3.fraction.FractionConversionException;
import org.apache.commons.math3.linear.Array2DRowFieldMatrix;
import org.apache.commons.math3.linear.Array2DRowRealMatrix;
import org.apache.commons.math3.linear.FieldMatrix;
import org.apache.commons.math3.linear.RealMatrix;
import org.apache.commons.math3.util.FastMath;

/**
 * Implementation of the Kolmogorov-Smirnov distribution.
 *
 * <p>
 * Treats the distribution of the two-sided {@code P(D_n < d)} where
 * {@code D_n = sup_x |G(x) - G_n (x)|} for the theoretical cdf {@code G} and
 * the empirical cdf {@code G_n}.
 * </p>
 * <p>
 * This implementation is based on [1] with certain quick decisions for extreme
 * values given in [2].
 * </p>
 * <p>
 * In short, when wanting to evaluate {@code P(D_n < d)}, the method in [1] is
 * to write {@code d = (k - h) / n} for positive integer {@code k} and
 * {@code 0 <= h < 1}. Then {@code P(D_n < d) = (n! / n^n) * t_kk}, where
 * {@code t_kk} is the {@code (k, k)}'th entry in the special matrix
 * {@code H^n}, i.e. {@code H} to the {@code n}'th power.
 * </p>
 * <p>
 * References:
 * <ul>
 * <li>[1] <a href="http://www.jstatsoft.org/v08/i18/">
 * Evaluating Kolmogorov's Distribution</a> by George Marsaglia, Wai
 * Wan Tsang, and Jingbo Wang</li>
 * <li>[2] <a href="http://www.jstatsoft.org/v39/i11/">
 * Computing the Two-Sided Kolmogorov-Smirnov Distribution</a> by Richard Simard
 * and Pierre L'Ecuyer</li>
 * </ul>
 * Note that [1] contains an error in computing h, refer to
 * <a href="https://issues.apache.org/jira/browse/MATH-437">MATH-437</a> for details.
 * </p>
 *
 * @see <a href="http://en.wikipedia.org/wiki/Kolmogorov-Smirnov_test">
 * Kolmogorov-Smirnov test (Wikipedia)</a>
 * @deprecated to be removed in version 4.0 -
 *  use {@link org.apache.commons.math3.stat.inference.KolmogorovSmirnovTest}
 */
public class KolmogorovSmirnovDistribution implements Serializable {

    /** Serializable version identifier. */
    private static final long serialVersionUID = -4670676796862967187L;

    /** Number of observations. */
    private int n;

    /**
     * @param n Number of observations
     * @throws NotStrictlyPositiveException if {@code n <= 0}
     */
    public KolmogorovSmirnovDistribution(int n)
        throws NotStrictlyPositiveException {
        if (n <= 0) {
            throw new NotStrictlyPositiveException(LocalizedFormats.NOT_POSITIVE_NUMBER_OF_SAMPLES, n);
        }

        this.n = n;
    }

    /**
     * Calculates {@code P(D_n < d)} using method described in [1] with quick
     * decisions for extreme values given in [2] (see above). The result is not
     * exact as with
     * {@link KolmogorovSmirnovDistribution#cdfExact(double)} because
     * calculations are based on {@code double} rather than
     * {@link org.apache.commons.math3.fraction.BigFraction}.
     *
     * @param d statistic
     * @return the two-sided probability of {@code P(D_n < d)}
     * @throws MathArithmeticException if algorithm fails to convert {@code h}
     * to a {@link org.apache.commons.math3.fraction.BigFraction} in expressing
     * {@code d} as {@code (k - h) / m} for integer {@code k, m} and
     * {@code 0 <= h < 1}.
     */
    public double cdf(double d) throws MathArithmeticException {
        return this.cdf(d, false);
    }

    /**
     * Calculates {@code P(D_n < d)} using method described in [1] with quick
     * decisions for extreme values given in [2] (see above). The result is
     * exact in the sense that BigFraction/BigReal is used everywhere at the
     * expense of very slow execution time. Almost never choose this in real
     * applications unless you are very sure; this is almost solely for
     * verification purposes. Normally, you would choose
     * {@link KolmogorovSmirnovDistribution#cdf(double)}
     *
     * @param d statistic
     * @return the two-sided probability of {@code P(D_n < d)}
     * @throws MathArithmeticException if algorithm fails to convert {@code h}
     * to a {@link org.apache.commons.math3.fraction.BigFraction} in expressing
     * {@code d} as {@code (k - h) / m} for integer {@code k, m} and
     * {@code 0 <= h < 1}.
     */
    public double cdfExact(double d) throws MathArithmeticException {
        return this.cdf(d, true);
    }

    /**
     * Calculates {@code P(D_n < d)} using method described in [1] with quick
     * decisions for extreme values given in [2] (see above).
     *
     * @param d statistic
     * @param exact whether the probability should be calculated exact using
     * {@link org.apache.commons.math3.fraction.BigFraction} everywhere at the
     * expense of very slow execution time, or if {@code double} should be used
     * convenient places to gain speed. Almost never choose {@code true} in real
     * applications unless you are very sure; {@code true} is almost solely for
     * verification purposes.
     * @return the two-sided probability of {@code P(D_n < d)}
     * @throws MathArithmeticException if algorithm fails to convert {@code h}
     * to a {@link org.apache.commons.math3.fraction.BigFraction} in expressing
     * {@code d} as {@code (k - h) / m} for integer {@code k, m} and
     * {@code 0 <= h < 1}.
     */
    public double cdf(double d, boolean exact) throws MathArithmeticException {

        final double ninv = 1 / ((double) n);
        final double ninvhalf = 0.5 * ninv;

        if (d <= ninvhalf) {

            return 0;

        } else if (ninvhalf < d && d <= ninv) {

            double res = 1;
            double f = 2 * d - ninv;

            // n! f^n = n*f * (n-1)*f * ... * 1*x
            for (int i = 1; i <= n; ++i) {
                res *= i * f;
            }

            return res;

        } else if (1 - ninv <= d && d < 1) {

            return 1 - 2 * FastMath.pow(1 - d, n);

        } else if (1 <= d) {

            return 1;
        }

        return exact ? exactK(d) : roundedK(d);
    }

    /**
     * Calculates the exact value of {@code P(D_n < d)} using method described
     * in [1] and {@link org.apache.commons.math3.fraction.BigFraction} (see
     * above).
     *
     * @param d statistic
     * @return the two-sided probability of {@code P(D_n < d)}
     * @throws MathArithmeticException if algorithm fails to convert {@code h}
     * to a {@link org.apache.commons.math3.fraction.BigFraction} in expressing
     * {@code d} as {@code (k - h) / m} for integer {@code k, m} and
     * {@code 0 <= h < 1}.
     */
    private double exactK(double d) throws MathArithmeticException {

        final int k = (int) FastMath.ceil(n * d);

        final FieldMatrix<BigFraction> H = this.createH(d);
        final FieldMatrix<BigFraction> Hpower = H.power(n);

        BigFraction pFrac = Hpower.getEntry(k - 1, k - 1);

        for (int i = 1; i <= n; ++i) {
            pFrac = pFrac.multiply(i).divide(n);
        }

        /*
         * BigFraction.doubleValue converts numerator to double and the
         * denominator to double and divides afterwards. That gives NaN quite
         * easy. This does not (scale is the number of digits):
         */
        return pFrac.bigDecimalValue(20, BigDecimal.ROUND_HALF_UP).doubleValue();
    }

    /**
     * Calculates {@code P(D_n < d)} using method described in [1] and doubles
     * (see above).
     *
     * @param d statistic
     * @return the two-sided probability of {@code P(D_n < d)}
     * @throws MathArithmeticException if algorithm fails to convert {@code h}
     * to a {@link org.apache.commons.math3.fraction.BigFraction} in expressing
     * {@code d} as {@code (k - h) / m} for integer {@code k, m} and
     * {@code 0 <= h < 1}.
     */
    private double roundedK(double d) throws MathArithmeticException {

        final int k = (int) FastMath.ceil(n * d);
        final FieldMatrix<BigFraction> HBigFraction = this.createH(d);
        final int m = HBigFraction.getRowDimension();

        /*
         * Here the rounding part comes into play: use
         * RealMatrix instead of FieldMatrix<BigFraction>
         */
        final RealMatrix H = new Array2DRowRealMatrix(m, m);

        for (int i = 0; i < m; ++i) {
            for (int j = 0; j < m; ++j) {
                H.setEntry(i, j, HBigFraction.getEntry(i, j).doubleValue());
            }
        }

        final RealMatrix Hpower = H.power(n);

        double pFrac = Hpower.getEntry(k - 1, k - 1);

        for (int i = 1; i <= n; ++i) {
            pFrac *= (double) i / (double) n;
        }

        return pFrac;
    }

    /***
     * Creates {@code H} of size {@code m x m} as described in [1] (see above).
     *
     * @param d statistic
     * @return H matrix
     * @throws NumberIsTooLargeException if fractional part is greater than 1
     * @throws FractionConversionException if algorithm fails to convert
     * {@code h} to a {@link org.apache.commons.math3.fraction.BigFraction} in
     * expressing {@code d} as {@code (k - h) / m} for integer {@code k, m} and
     * {@code 0 <= h < 1}.
     */
    private FieldMatrix<BigFraction> createH(double d)
            throws NumberIsTooLargeException, FractionConversionException {

        int k = (int) FastMath.ceil(n * d);

        int m = 2 * k - 1;
        double hDouble = k - n * d;

        if (hDouble >= 1) {
            throw new NumberIsTooLargeException(hDouble, 1.0, false);
        }

        BigFraction h = null;

        try {
            h = new BigFraction(hDouble, 1.0e-20, 10000);
        } catch (FractionConversionException e1) {
            try {
                h = new BigFraction(hDouble, 1.0e-10, 10000);
            } catch (FractionConversionException e2) {
                h = new BigFraction(hDouble, 1.0e-5, 10000);
            }
        }

        final BigFraction[][] Hdata = new BigFraction[m][m];

        /*
         * Start by filling everything with either 0 or 1.
         */
        for (int i = 0; i < m; ++i) {
            for (int j = 0; j < m; ++j) {
                if (i - j + 1 < 0) {
                    Hdata[i][j] = BigFraction.ZERO;
                } else {
                    Hdata[i][j] = BigFraction.ONE;
                }
            }
        }

        /*
         * Setting up power-array to avoid calculating the same value twice:
         * hPowers[0] = h^1 ... hPowers[m-1] = h^m
         */
        final BigFraction[] hPowers = new BigFraction[m];
        hPowers[0] = h;
        for (int i = 1; i < m; ++i) {
            hPowers[i] = h.multiply(hPowers[i - 1]);
        }

        /*
         * First column and last row has special values (each other reversed).
         */
        for (int i = 0; i < m; ++i) {
            Hdata[i][0] = Hdata[i][0].subtract(hPowers[i]);
            Hdata[m - 1][i] = Hdata[m - 1][i].subtract(hPowers[m - i - 1]);
        }

        /*
         * [1] states: "For 1/2 < h < 1 the bottom left element of the matrix
         * should be (1 - 2*h^m + (2h - 1)^m )/m!" Since 0 <= h < 1, then if h >
         * 1/2 is sufficient to check:
         */
        if (h.compareTo(BigFraction.ONE_HALF) == 1) {
            Hdata[m - 1][0] = Hdata[m - 1][0].add(h.multiply(2).subtract(1).pow(m));
        }

        /*
         * Aside from the first column and last row, the (i, j)-th element is
         * 1/(i - j + 1)! if i - j + 1 >= 0, else 0. 1's and 0's are already
         * put, so only division with (i - j + 1)! is needed in the elements
         * that have 1's. There is no need to calculate (i - j + 1)! and then
         * divide - small steps avoid overflows.
         *
         * Note that i - j + 1 > 0 <=> i + 1 > j instead of j'ing all the way to
         * m. Also note that it is started at g = 2 because dividing by 1 isn't
         * really necessary.
         */
        for (int i = 0; i < m; ++i) {
            for (int j = 0; j < i + 1; ++j) {
                if (i - j + 1 > 0) {
                    for (int g = 2; g <= i - j + 1; ++g) {
                        Hdata[i][j] = Hdata[i][j].divide(g);
                    }
                }
            }
        }

        return new Array2DRowFieldMatrix<BigFraction>(BigFractionField.getInstance(), Hdata);
    }
}
