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
package org.apache.commons.math3.stat.inference;

import org.apache.commons.math3.distribution.ChiSquaredDistribution;
import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.MaxCountExceededException;
import org.apache.commons.math3.exception.NotPositiveException;
import org.apache.commons.math3.exception.NotStrictlyPositiveException;
import org.apache.commons.math3.exception.OutOfRangeException;
import org.apache.commons.math3.exception.ZeroException;
import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.util.FastMath;
import org.apache.commons.math3.util.MathArrays;

/**
 * Implements <a href="http://en.wikipedia.org/wiki/G-test">G Test</a>
 * statistics.
 *
 * <p>This is known in statistical genetics as the McDonald-Kreitman test.
 * The implementation handles both known and unknown distributions.</p>
 *
 * <p>Two samples tests can be used when the distribution is unknown <i>a priori</i>
 * but provided by one sample, or when the hypothesis under test is that the two
 * samples come from the same underlying distribution.</p>
 *
 * @since 3.1
 */
public class GTest {

    /**
     * Computes the <a href="http://en.wikipedia.org/wiki/G-test">G statistic
     * for Goodness of Fit</a> comparing {@code observed} and {@code expected}
     * frequency counts.
     *
     * <p>This statistic can be used to perform a G test (Log-Likelihood Ratio
     * Test) evaluating the null hypothesis that the observed counts follow the
     * expected distribution.</p>
     *
     * <p><strong>Preconditions</strong>: <ul>
     * <li>Expected counts must all be positive. </li>
     * <li>Observed counts must all be &ge; 0. </li>
     * <li>The observed and expected arrays must have the same length and their
     * common length must be at least 2. </li></ul></p>
     *
     * <p>If any of the preconditions are not met, a
     * {@code MathIllegalArgumentException} is thrown.</p>
     *
     * <p><strong>Note:</strong>This implementation rescales the
     * {@code expected} array if necessary to ensure that the sum of the
     * expected and observed counts are equal.</p>
     *
     * @param observed array of observed frequency counts
     * @param expected array of expected frequency counts
     * @return G-Test statistic
     * @throws NotPositiveException if {@code observed} has negative entries
     * @throws NotStrictlyPositiveException if {@code expected} has entries that
     * are not strictly positive
     * @throws DimensionMismatchException if the array lengths do not match or
     * are less than 2.
     */
    public double g(final double[] expected, final long[] observed)
            throws NotPositiveException, NotStrictlyPositiveException,
            DimensionMismatchException {

        if (expected.length < 2) {
            throw new DimensionMismatchException(expected.length, 2);
        }
        if (expected.length != observed.length) {
            throw new DimensionMismatchException(expected.length, observed.length);
        }
        MathArrays.checkPositive(expected);
        MathArrays.checkNonNegative(observed);

        double sumExpected = 0d;
        double sumObserved = 0d;
        for (int i = 0; i < observed.length; i++) {
            sumExpected += expected[i];
            sumObserved += observed[i];
        }
        double ratio = 1d;
        boolean rescale = false;
        if (FastMath.abs(sumExpected - sumObserved) > 10E-6) {
            ratio = sumObserved / sumExpected;
            rescale = true;
        }
        double sum = 0d;
        for (int i = 0; i < observed.length; i++) {
            final double dev = rescale ?
                    FastMath.log((double) observed[i] / (ratio * expected[i])) :
                        FastMath.log((double) observed[i] / expected[i]);
            sum += ((double) observed[i]) * dev;
        }
        return 2d * sum;
    }

    /**
     * Returns the <i>observed significance level</i>, or <a href=
     * "http://www.cas.lancs.ac.uk/glossary_v1.1/hyptest.html#pvalue"> p-value</a>,
     * associated with a G-Test for goodness of fit</a> comparing the
     * {@code observed} frequency counts to those in the {@code expected} array.
     *
     * <p>The number returned is the smallest significance level at which one
     * can reject the null hypothesis that the observed counts conform to the
     * frequency distribution described by the expected counts.</p>
     *
     * <p>The probability returned is the tail probability beyond
     * {@link #g(double[], long[]) g(expected, observed)}
     * in the ChiSquare distribution with degrees of freedom one less than the
     * common length of {@code expected} and {@code observed}.</p>
     *
     * <p> <strong>Preconditions</strong>: <ul>
     * <li>Expected counts must all be positive. </li>
     * <li>Observed counts must all be &ge; 0. </li>
     * <li>The observed and expected arrays must have the
     * same length and their common length must be at least 2.</li>
     * </ul></p>
     *
     * <p>If any of the preconditions are not met, a
     * {@code MathIllegalArgumentException} is thrown.</p>
     *
     * <p><strong>Note:</strong>This implementation rescales the
     * {@code expected} array if necessary to ensure that the sum of the
     *  expected and observed counts are equal.</p>
     *
     * @param observed array of observed frequency counts
     * @param expected array of expected frequency counts
     * @return p-value
     * @throws NotPositiveException if {@code observed} has negative entries
     * @throws NotStrictlyPositiveException if {@code expected} has entries that
     * are not strictly positive
     * @throws DimensionMismatchException if the array lengths do not match or
     * are less than 2.
     * @throws MaxCountExceededException if an error occurs computing the
     * p-value.
     */
    public double gTest(final double[] expected, final long[] observed)
            throws NotPositiveException, NotStrictlyPositiveException,
            DimensionMismatchException, MaxCountExceededException {

        // pass a null rng to avoid unneeded overhead as we will not sample from this distribution
        final ChiSquaredDistribution distribution =
                new ChiSquaredDistribution(null, expected.length - 1.0);
        return 1.0 - distribution.cumulativeProbability(g(expected, observed));
    }

    /**
     * Returns the intrinsic (Hardy-Weinberg proportions) p-Value, as described
     * in p64-69 of McDonald, J.H. 2009. Handbook of Biological Statistics
     * (2nd ed.). Sparky House Publishing, Baltimore, Maryland.
     *
     * <p> The probability returned is the tail probability beyond
     * {@link #g(double[], long[]) g(expected, observed)}
     * in the ChiSquare distribution with degrees of freedom two less than the
     * common length of {@code expected} and {@code observed}.</p>
     *
     * @param observed array of observed frequency counts
     * @param expected array of expected frequency counts
     * @return p-value
     * @throws NotPositiveException if {@code observed} has negative entries
     * @throws NotStrictlyPositiveException {@code expected} has entries that are
     * not strictly positive
     * @throws DimensionMismatchException if the array lengths do not match or
     * are less than 2.
     * @throws MaxCountExceededException if an error occurs computing the
     * p-value.
     */
    public double gTestIntrinsic(final double[] expected, final long[] observed)
            throws NotPositiveException, NotStrictlyPositiveException,
            DimensionMismatchException, MaxCountExceededException {

        // pass a null rng to avoid unneeded overhead as we will not sample from this distribution
        final ChiSquaredDistribution distribution =
                new ChiSquaredDistribution(null, expected.length - 2.0);
        return 1.0 - distribution.cumulativeProbability(g(expected, observed));
    }

    /**
     * Performs a G-Test (Log-Likelihood Ratio Test) for goodness of fit
     * evaluating the null hypothesis that the observed counts conform to the
     * frequency distribution described by the expected counts, with
     * significance level {@code alpha}. Returns true iff the null
     * hypothesis can be rejected with {@code 100 * (1 - alpha)} percent confidence.
     *
     * <p><strong>Example:</strong><br> To test the hypothesis that
     * {@code observed} follows {@code expected} at the 99% level,
     * use </p><p>
     * {@code gTest(expected, observed, 0.01)}</p>
     *
     * <p>Returns true iff {@link #gTest(double[], long[])
     *  gTestGoodnessOfFitPValue(expected, observed)} < alpha</p>
     *
     * <p><strong>Preconditions</strong>: <ul>
     * <li>Expected counts must all be positive. </li>
     * <li>Observed counts must all be &ge; 0. </li>
     * <li>The observed and expected arrays must have the same length and their
     * common length must be at least 2.
     * <li> {@code 0 < alpha < 0.5} </li></ul></p>
     *
     * <p>If any of the preconditions are not met, a
     * {@code MathIllegalArgumentException} is thrown.</p>
     *
     * <p><strong>Note:</strong>This implementation rescales the
     * {@code expected} array if necessary to ensure that the sum of the
     * expected and observed counts are equal.</p>
     *
     * @param observed array of observed frequency counts
     * @param expected array of expected frequency counts
     * @param alpha significance level of the test
     * @return true iff null hypothesis can be rejected with confidence 1 -
     * alpha
     * @throws NotPositiveException if {@code observed} has negative entries
     * @throws NotStrictlyPositiveException if {@code expected} has entries that
     * are not strictly positive
     * @throws DimensionMismatchException if the array lengths do not match or
     * are less than 2.
     * @throws MaxCountExceededException if an error occurs computing the
     * p-value.
     * @throws OutOfRangeException if alpha is not strictly greater than zero
     * and less than or equal to 0.5
     */
    public boolean gTest(final double[] expected, final long[] observed,
            final double alpha)
            throws NotPositiveException, NotStrictlyPositiveException,
            DimensionMismatchException, OutOfRangeException, MaxCountExceededException {

        if ((alpha <= 0) || (alpha > 0.5)) {
            throw new OutOfRangeException(LocalizedFormats.OUT_OF_BOUND_SIGNIFICANCE_LEVEL,
                    alpha, 0, 0.5);
        }
        return gTest(expected, observed) < alpha;
    }

    /**
     * Calculates the <a href=
     * "http://en.wikipedia.org/wiki/Entropy_%28information_theory%29">Shannon
     * entropy</a> for 2 Dimensional Matrix.  The value returned is the entropy
     * of the vector formed by concatenating the rows (or columns) of {@code k}
     * to form a vector. See {@link #entropy(long[])}.
     *
     * @param k 2 Dimensional Matrix of long values (for ex. the counts of a
     * trials)
     * @return Shannon Entropy of the given Matrix
     *
     */
    private double entropy(final long[][] k) {
        double h = 0d;
        double sum_k = 0d;
        for (int i = 0; i < k.length; i++) {
            for (int j = 0; j < k[i].length; j++) {
                sum_k += (double) k[i][j];
            }
        }
        for (int i = 0; i < k.length; i++) {
            for (int j = 0; j < k[i].length; j++) {
                if (k[i][j] != 0) {
                    final double p_ij = (double) k[i][j] / sum_k;
                    h += p_ij * FastMath.log(p_ij);
                }
            }
        }
        return -h;
    }

    /**
     * Calculates the <a href="http://en.wikipedia.org/wiki/Entropy_%28information_theory%29">
     * Shannon entropy</a> for a vector.  The values of {@code k} are taken to be
     * incidence counts of the values of a random variable. What is returned is <br/>
     * &sum;p<sub>i</sub>log(p<sub>i</sub><br/>
     * where p<sub>i</sub> = k[i] / (sum of elements in k)
     *
     * @param k Vector (for ex. Row Sums of a trials)
     * @return Shannon Entropy of the given Vector
     *
     */
    private double entropy(final long[] k) {
        double h = 0d;
        double sum_k = 0d;
        for (int i = 0; i < k.length; i++) {
            sum_k += (double) k[i];
        }
        for (int i = 0; i < k.length; i++) {
            if (k[i] != 0) {
                final double p_i = (double) k[i] / sum_k;
                h += p_i * FastMath.log(p_i);
            }
        }
        return -h;
    }

    /**
     * <p>Computes a G (Log-Likelihood Ratio) two sample test statistic for
     * independence comparing frequency counts in
     * {@code observed1} and {@code observed2}. The sums of frequency
     * counts in the two samples are not required to be the same. The formula
     * used to compute the test statistic is </p>
     *
     * <p>{@code 2 * totalSum * [H(rowSums) + H(colSums) - H(k)]}</p>
     *
     * <p> where {@code H} is the
     * <a href="http://en.wikipedia.org/wiki/Entropy_%28information_theory%29">
     * Shannon Entropy</a> of the random variable formed by viewing the elements
     * of the argument array as incidence counts; <br/>
     * {@code k} is a matrix with rows {@code [observed1, observed2]}; <br/>
     * {@code rowSums, colSums} are the row/col sums of {@code k}; <br>
     * and {@code totalSum} is the overall sum of all entries in {@code k}.</p>
     *
     * <p>This statistic can be used to perform a G test evaluating the null
     * hypothesis that both observed counts are independent </p>
     *
     * <p> <strong>Preconditions</strong>: <ul>
     * <li>Observed counts must be non-negative. </li>
     * <li>Observed counts for a specific bin must not both be zero. </li>
     * <li>Observed counts for a specific sample must not all be  0. </li>
     * <li>The arrays {@code observed1} and {@code observed2} must have
     * the same length and their common length must be at least 2. </li></ul></p>
     *
     * <p>If any of the preconditions are not met, a
     * {@code MathIllegalArgumentException} is thrown.</p>
     *
     * @param observed1 array of observed frequency counts of the first data set
     * @param observed2 array of observed frequency counts of the second data
     * set
     * @return G-Test statistic
     * @throws DimensionMismatchException the the lengths of the arrays do not
     * match or their common length is less than 2
     * @throws NotPositiveException if any entry in {@code observed1} or
     * {@code observed2} is negative
     * @throws ZeroException if either all counts of
     * {@code observed1} or {@code observed2} are zero, or if the count
     * at the same index is zero for both arrays.
     */
    public double gDataSetsComparison(final long[] observed1, final long[] observed2)
            throws DimensionMismatchException, NotPositiveException, ZeroException {

        // Make sure lengths are same
        if (observed1.length < 2) {
            throw new DimensionMismatchException(observed1.length, 2);
        }
        if (observed1.length != observed2.length) {
            throw new DimensionMismatchException(observed1.length, observed2.length);
        }

        // Ensure non-negative counts
        MathArrays.checkNonNegative(observed1);
        MathArrays.checkNonNegative(observed2);

        // Compute and compare count sums
        long countSum1 = 0;
        long countSum2 = 0;

        // Compute and compare count sums
        final long[] collSums = new long[observed1.length];
        final long[][] k = new long[2][observed1.length];

        for (int i = 0; i < observed1.length; i++) {
            if (observed1[i] == 0 && observed2[i] == 0) {
                throw new ZeroException(LocalizedFormats.OBSERVED_COUNTS_BOTTH_ZERO_FOR_ENTRY, i);
            } else {
                countSum1 += observed1[i];
                countSum2 += observed2[i];
                collSums[i] = observed1[i] + observed2[i];
                k[0][i] = observed1[i];
                k[1][i] = observed2[i];
            }
        }
        // Ensure neither sample is uniformly 0
        if (countSum1 == 0 || countSum2 == 0) {
            throw new ZeroException();
        }
        final long[] rowSums = {countSum1, countSum2};
        final double sum = (double) countSum1 + (double) countSum2;
        return 2 * sum * (entropy(rowSums) + entropy(collSums) - entropy(k));
    }

    /**
     * Calculates the root log-likelihood ratio for 2 state Datasets. See
     * {@link #gDataSetsComparison(long[], long[] )}.
     *
     * <p>Given two events A and B, let k11 be the number of times both events
     * occur, k12 the incidence of B without A, k21 the count of A without B,
     * and k22 the number of times neither A nor B occurs.  What is returned
     * by this method is </p>
     *
     * <p>{@code (sgn) sqrt(gValueDataSetsComparison({k11, k12}, {k21, k22})}</p>
     *
     * <p>where {@code sgn} is -1 if {@code k11 / (k11 + k12) < k21 / (k21 + k22))};<br/>
     * 1 otherwise.</p>
     *
     * <p>Signed root LLR has two advantages over the basic LLR: a) it is positive
     * where k11 is bigger than expected, negative where it is lower b) if there is
     * no difference it is asymptotically normally distributed. This allows one
     * to talk about "number of standard deviations" which is a more common frame
     * of reference than the chi^2 distribution.</p>
     *
     * @param k11 number of times the two events occurred together (AB)
     * @param k12 number of times the second event occurred WITHOUT the
     * first event (notA,B)
     * @param k21 number of times the first event occurred WITHOUT the
     * second event (A, notB)
     * @param k22 number of times something else occurred (i.e. was neither
     * of these events (notA, notB)
     * @return root log-likelihood ratio
     *
     */
    public double rootLogLikelihoodRatio(final long k11, long k12,
            final long k21, final long k22) {
        final double llr = gDataSetsComparison(
                new long[]{k11, k12}, new long[]{k21, k22});
        double sqrt = FastMath.sqrt(llr);
        if ((double) k11 / (k11 + k12) < (double) k21 / (k21 + k22)) {
            sqrt = -sqrt;
        }
        return sqrt;
    }

    /**
     * <p>Returns the <i>observed significance level</i>, or <a href=
     * "http://www.cas.lancs.ac.uk/glossary_v1.1/hyptest.html#pvalue">
     * p-value</a>, associated with a G-Value (Log-Likelihood Ratio) for two
     * sample test comparing bin frequency counts in {@code observed1} and
     * {@code observed2}.</p>
     *
     * <p>The number returned is the smallest significance level at which one
     * can reject the null hypothesis that the observed counts conform to the
     * same distribution. </p>
     *
     * <p>See {@link #gTest(double[], long[])} for details
     * on how the p-value is computed.  The degrees of of freedom used to
     * perform the test is one less than the common length of the input observed
     * count arrays.</p>
     *
     * <p><strong>Preconditions</strong>:
     * <ul> <li>Observed counts must be non-negative. </li>
     * <li>Observed counts for a specific bin must not both be zero. </li>
     * <li>Observed counts for a specific sample must not all be 0. </li>
     * <li>The arrays {@code observed1} and {@code observed2} must
     * have the same length and their common length must be at least 2. </li>
     * </ul><p>
     * <p> If any of the preconditions are not met, a
     * {@code MathIllegalArgumentException} is thrown.</p>
     *
     * @param observed1 array of observed frequency counts of the first data set
     * @param observed2 array of observed frequency counts of the second data
     * set
     * @return p-value
     * @throws DimensionMismatchException the the length of the arrays does not
     * match or their common length is less than 2
     * @throws NotPositiveException if any of the entries in {@code observed1} or
     * {@code observed2} are negative
     * @throws ZeroException if either all counts of {@code observed1} or
     * {@code observed2} are zero, or if the count at some index is
     * zero for both arrays
     * @throws MaxCountExceededException if an error occurs computing the
     * p-value.
     */
    public double gTestDataSetsComparison(final long[] observed1,
            final long[] observed2)
            throws DimensionMismatchException, NotPositiveException, ZeroException,
            MaxCountExceededException {

        // pass a null rng to avoid unneeded overhead as we will not sample from this distribution
        final ChiSquaredDistribution distribution =
                new ChiSquaredDistribution(null, (double) observed1.length - 1);
        return 1 - distribution.cumulativeProbability(
                gDataSetsComparison(observed1, observed2));
    }

    /**
     * <p>Performs a G-Test (Log-Likelihood Ratio Test) comparing two binned
     * data sets. The test evaluates the null hypothesis that the two lists
     * of observed counts conform to the same frequency distribution, with
     * significance level {@code alpha}. Returns true iff the null
     * hypothesis can be rejected  with 100 * (1 - alpha) percent confidence.
     * </p>
     * <p>See {@link #gDataSetsComparison(long[], long[])} for details
     * on the formula used to compute the G (LLR) statistic used in the test and
     * {@link #gTest(double[], long[])} for information on how
     * the observed significance level is computed. The degrees of of freedom used
     * to perform the test is one less than the common length of the input observed
     * count arrays. </p>
     *
     * <strong>Preconditions</strong>: <ul>
     * <li>Observed counts must be non-negative. </li>
     * <li>Observed counts for a specific bin must not both be zero. </li>
     * <li>Observed counts for a specific sample must not all be 0. </li>
     * <li>The arrays {@code observed1} and {@code observed2} must
     * have the same length and their common length must be at least 2. </li>
     * <li>{@code 0 < alpha < 0.5} </li></ul></p>
     *
     * <p>If any of the preconditions are not met, a
     * {@code MathIllegalArgumentException} is thrown.</p>
     *
     * @param observed1 array of observed frequency counts of the first data set
     * @param observed2 array of observed frequency counts of the second data
     * set
     * @param alpha significance level of the test
     * @return true iff null hypothesis can be rejected with confidence 1 -
     * alpha
     * @throws DimensionMismatchException the the length of the arrays does not
     * match
     * @throws NotPositiveException if any of the entries in {@code observed1} or
     * {@code observed2} are negative
     * @throws ZeroException if either all counts of {@code observed1} or
     * {@code observed2} are zero, or if the count at some index is
     * zero for both arrays
     * @throws OutOfRangeException if {@code alpha} is not in the range
     * (0, 0.5]
     * @throws MaxCountExceededException if an error occurs performing the test
     */
    public boolean gTestDataSetsComparison(
            final long[] observed1,
            final long[] observed2,
            final double alpha)
            throws DimensionMismatchException, NotPositiveException,
            ZeroException, OutOfRangeException, MaxCountExceededException {

        if (alpha <= 0 || alpha > 0.5) {
            throw new OutOfRangeException(
                    LocalizedFormats.OUT_OF_BOUND_SIGNIFICANCE_LEVEL, alpha, 0, 0.5);
        }
        return gTestDataSetsComparison(observed1, observed2) < alpha;
    }
}
