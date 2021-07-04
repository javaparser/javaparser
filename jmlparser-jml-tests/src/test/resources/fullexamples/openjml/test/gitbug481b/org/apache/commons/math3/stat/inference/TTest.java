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

import org.apache.commons.math3.distribution.TDistribution;
import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.MathIllegalArgumentException;
import org.apache.commons.math3.exception.MaxCountExceededException;
import org.apache.commons.math3.exception.NoDataException;
import org.apache.commons.math3.exception.NotStrictlyPositiveException;
import org.apache.commons.math3.exception.NullArgumentException;
import org.apache.commons.math3.exception.NumberIsTooSmallException;
import org.apache.commons.math3.exception.OutOfRangeException;
import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.stat.StatUtils;
import org.apache.commons.math3.stat.descriptive.StatisticalSummary;
import org.apache.commons.math3.util.FastMath;

/**
 * An implementation for Student's t-tests.
 * <p>
 * Tests can be:<ul>
 * <li>One-sample or two-sample</li>
 * <li>One-sided or two-sided</li>
 * <li>Paired or unpaired (for two-sample tests)</li>
 * <li>Homoscedastic (equal variance assumption) or heteroscedastic
 * (for two sample tests)</li>
 * <li>Fixed significance level (boolean-valued) or returning p-values.
 * </li></ul></p>
 * <p>
 * Test statistics are available for all tests.  Methods including "Test" in
 * in their names perform tests, all other methods return t-statistics.  Among
 * the "Test" methods, <code>double-</code>valued methods return p-values;
 * <code>boolean-</code>valued methods perform fixed significance level tests.
 * Significance levels are always specified as numbers between 0 and 0.5
 * (e.g. tests at the 95% level  use <code>alpha=0.05</code>).</p>
 * <p>
 * Input to tests can be either <code>double[]</code> arrays or
 * {@link StatisticalSummary} instances.</p><p>
 * Uses commons-math {@link org.apache.commons.math3.distribution.TDistribution}
 * implementation to estimate exact p-values.</p>
 *
 */
public class TTest {
    /**
     * Computes a paired, 2-sample t-statistic based on the data in the input
     * arrays.  The t-statistic returned is equivalent to what would be returned by
     * computing the one-sample t-statistic {@link #t(double, double[])}, with
     * <code>mu = 0</code> and the sample array consisting of the (signed)
     * differences between corresponding entries in <code>sample1</code> and
     * <code>sample2.</code>
     * <p>
     * <strong>Preconditions</strong>: <ul>
     * <li>The input arrays must have the same length and their common length
     * must be at least 2.
     * </li></ul></p>
     *
     * @param sample1 array of sample data values
     * @param sample2 array of sample data values
     * @return t statistic
     * @throws NullArgumentException if the arrays are <code>null</code>
     * @throws NoDataException if the arrays are empty
     * @throws DimensionMismatchException if the length of the arrays is not equal
     * @throws NumberIsTooSmallException if the length of the arrays is &lt; 2
     */
    public double pairedT(final double[] sample1, final double[] sample2)
        throws NullArgumentException, NoDataException,
        DimensionMismatchException, NumberIsTooSmallException {

        checkSampleData(sample1);
        checkSampleData(sample2);
        double meanDifference = StatUtils.meanDifference(sample1, sample2);
        return t(meanDifference, 0,
                 StatUtils.varianceDifference(sample1, sample2, meanDifference),
                 sample1.length);

    }

    /**
     * Returns the <i>observed significance level</i>, or
     * <i> p-value</i>, associated with a paired, two-sample, two-tailed t-test
     * based on the data in the input arrays.
     * <p>
     * The number returned is the smallest significance level
     * at which one can reject the null hypothesis that the mean of the paired
     * differences is 0 in favor of the two-sided alternative that the mean paired
     * difference is not equal to 0. For a one-sided test, divide the returned
     * value by 2.</p>
     * <p>
     * This test is equivalent to a one-sample t-test computed using
     * {@link #tTest(double, double[])} with <code>mu = 0</code> and the sample
     * array consisting of the signed differences between corresponding elements of
     * <code>sample1</code> and <code>sample2.</code></p>
     * <p>
     * <strong>Usage Note:</strong><br>
     * The validity of the p-value depends on the assumptions of the parametric
     * t-test procedure, as discussed
     * <a href="http://www.basic.nwu.edu/statguidefiles/ttest_unpaired_ass_viol.html">
     * here</a></p>
     * <p>
     * <strong>Preconditions</strong>: <ul>
     * <li>The input array lengths must be the same and their common length must
     * be at least 2.
     * </li></ul></p>
     *
     * @param sample1 array of sample data values
     * @param sample2 array of sample data values
     * @return p-value for t-test
     * @throws NullArgumentException if the arrays are <code>null</code>
     * @throws NoDataException if the arrays are empty
     * @throws DimensionMismatchException if the length of the arrays is not equal
     * @throws NumberIsTooSmallException if the length of the arrays is &lt; 2
     * @throws MaxCountExceededException if an error occurs computing the p-value
     */
    public double pairedTTest(final double[] sample1, final double[] sample2)
        throws NullArgumentException, NoDataException, DimensionMismatchException,
        NumberIsTooSmallException, MaxCountExceededException {

        double meanDifference = StatUtils.meanDifference(sample1, sample2);
        return tTest(meanDifference, 0,
                StatUtils.varianceDifference(sample1, sample2, meanDifference),
                sample1.length);

    }

    /**
     * Performs a paired t-test evaluating the null hypothesis that the
     * mean of the paired differences between <code>sample1</code> and
     * <code>sample2</code> is 0 in favor of the two-sided alternative that the
     * mean paired difference is not equal to 0, with significance level
     * <code>alpha</code>.
     * <p>
     * Returns <code>true</code> iff the null hypothesis can be rejected with
     * confidence <code>1 - alpha</code>.  To perform a 1-sided test, use
     * <code>alpha * 2</code></p>
     * <p>
     * <strong>Usage Note:</strong><br>
     * The validity of the test depends on the assumptions of the parametric
     * t-test procedure, as discussed
     * <a href="http://www.basic.nwu.edu/statguidefiles/ttest_unpaired_ass_viol.html">
     * here</a></p>
     * <p>
     * <strong>Preconditions</strong>: <ul>
     * <li>The input array lengths must be the same and their common length
     * must be at least 2.
     * </li>
     * <li> <code> 0 &lt; alpha &lt; 0.5 </code>
     * </li></ul></p>
     *
     * @param sample1 array of sample data values
     * @param sample2 array of sample data values
     * @param alpha significance level of the test
     * @return true if the null hypothesis can be rejected with
     * confidence 1 - alpha
     * @throws NullArgumentException if the arrays are <code>null</code>
     * @throws NoDataException if the arrays are empty
     * @throws DimensionMismatchException if the length of the arrays is not equal
     * @throws NumberIsTooSmallException if the length of the arrays is &lt; 2
     * @throws OutOfRangeException if <code>alpha</code> is not in the range (0, 0.5]
     * @throws MaxCountExceededException if an error occurs computing the p-value
     */
    public boolean pairedTTest(final double[] sample1, final double[] sample2,
                               final double alpha)
        throws NullArgumentException, NoDataException, DimensionMismatchException,
        NumberIsTooSmallException, OutOfRangeException, MaxCountExceededException {

        checkSignificanceLevel(alpha);
        return pairedTTest(sample1, sample2) < alpha;

    }

    /**
     * Computes a <a href="http://www.itl.nist.gov/div898/handbook/prc/section2/prc22.htm#formula">
     * t statistic </a> given observed values and a comparison constant.
     * <p>
     * This statistic can be used to perform a one sample t-test for the mean.
     * </p><p>
     * <strong>Preconditions</strong>: <ul>
     * <li>The observed array length must be at least 2.
     * </li></ul></p>
     *
     * @param mu comparison constant
     * @param observed array of values
     * @return t statistic
     * @throws NullArgumentException if <code>observed</code> is <code>null</code>
     * @throws NumberIsTooSmallException if the length of <code>observed</code> is &lt; 2
     */
    public double t(final double mu, final double[] observed)
        throws NullArgumentException, NumberIsTooSmallException {

        checkSampleData(observed);
        // No try-catch or advertised exception because args have just been checked
        return t(StatUtils.mean(observed), mu, StatUtils.variance(observed),
                observed.length);

    }

    /**
     * Computes a <a href="http://www.itl.nist.gov/div898/handbook/prc/section2/prc22.htm#formula">
     * t statistic </a> to use in comparing the mean of the dataset described by
     * <code>sampleStats</code> to <code>mu</code>.
     * <p>
     * This statistic can be used to perform a one sample t-test for the mean.
     * </p><p>
     * <strong>Preconditions</strong>: <ul>
     * <li><code>observed.getN() &ge; 2</code>.
     * </li></ul></p>
     *
     * @param mu comparison constant
     * @param sampleStats DescriptiveStatistics holding sample summary statitstics
     * @return t statistic
     * @throws NullArgumentException if <code>sampleStats</code> is <code>null</code>
     * @throws NumberIsTooSmallException if the number of samples is &lt; 2
     */
    public double t(final double mu, final StatisticalSummary sampleStats)
        throws NullArgumentException, NumberIsTooSmallException {

        checkSampleData(sampleStats);
        return t(sampleStats.getMean(), mu, sampleStats.getVariance(),
                 sampleStats.getN());

    }

    /**
     * Computes a 2-sample t statistic,  under the hypothesis of equal
     * subpopulation variances.  To compute a t-statistic without the
     * equal variances hypothesis, use {@link #t(double[], double[])}.
     * <p>
     * This statistic can be used to perform a (homoscedastic) two-sample
     * t-test to compare sample means.</p>
     * <p>
     * The t-statistic is</p>
     * <p>
     * &nbsp;&nbsp;<code>  t = (m1 - m2) / (sqrt(1/n1 +1/n2) sqrt(var))</code>
     * </p><p>
     * where <strong><code>n1</code></strong> is the size of first sample;
     * <strong><code> n2</code></strong> is the size of second sample;
     * <strong><code> m1</code></strong> is the mean of first sample;
     * <strong><code> m2</code></strong> is the mean of second sample</li>
     * </ul>
     * and <strong><code>var</code></strong> is the pooled variance estimate:
     * </p><p>
     * <code>var = sqrt(((n1 - 1)var1 + (n2 - 1)var2) / ((n1-1) + (n2-1)))</code>
     * </p><p>
     * with <strong><code>var1</code></strong> the variance of the first sample and
     * <strong><code>var2</code></strong> the variance of the second sample.
     * </p><p>
     * <strong>Preconditions</strong>: <ul>
     * <li>The observed array lengths must both be at least 2.
     * </li></ul></p>
     *
     * @param sample1 array of sample data values
     * @param sample2 array of sample data values
     * @return t statistic
     * @throws NullArgumentException if the arrays are <code>null</code>
     * @throws NumberIsTooSmallException if the length of the arrays is &lt; 2
     */
    public double homoscedasticT(final double[] sample1, final double[] sample2)
        throws NullArgumentException, NumberIsTooSmallException {

        checkSampleData(sample1);
        checkSampleData(sample2);
        // No try-catch or advertised exception because args have just been checked
        return homoscedasticT(StatUtils.mean(sample1), StatUtils.mean(sample2),
                              StatUtils.variance(sample1), StatUtils.variance(sample2),
                              sample1.length, sample2.length);

    }

    /**
     * Computes a 2-sample t statistic, without the hypothesis of equal
     * subpopulation variances.  To compute a t-statistic assuming equal
     * variances, use {@link #homoscedasticT(double[], double[])}.
     * <p>
     * This statistic can be used to perform a two-sample t-test to compare
     * sample means.</p>
     * <p>
     * The t-statistic is</p>
     * <p>
     * &nbsp;&nbsp; <code>  t = (m1 - m2) / sqrt(var1/n1 + var2/n2)</code>
     * </p><p>
     *  where <strong><code>n1</code></strong> is the size of the first sample
     * <strong><code> n2</code></strong> is the size of the second sample;
     * <strong><code> m1</code></strong> is the mean of the first sample;
     * <strong><code> m2</code></strong> is the mean of the second sample;
     * <strong><code> var1</code></strong> is the variance of the first sample;
     * <strong><code> var2</code></strong> is the variance of the second sample;
     * </p><p>
     * <strong>Preconditions</strong>: <ul>
     * <li>The observed array lengths must both be at least 2.
     * </li></ul></p>
     *
     * @param sample1 array of sample data values
     * @param sample2 array of sample data values
     * @return t statistic
     * @throws NullArgumentException if the arrays are <code>null</code>
     * @throws NumberIsTooSmallException if the length of the arrays is &lt; 2
     */
    public double t(final double[] sample1, final double[] sample2)
        throws NullArgumentException, NumberIsTooSmallException {

        checkSampleData(sample1);
        checkSampleData(sample2);
        // No try-catch or advertised exception because args have just been checked
        return t(StatUtils.mean(sample1), StatUtils.mean(sample2),
                 StatUtils.variance(sample1), StatUtils.variance(sample2),
                 sample1.length, sample2.length);

    }

    /**
     * Computes a 2-sample t statistic </a>, comparing the means of the datasets
     * described by two {@link StatisticalSummary} instances, without the
     * assumption of equal subpopulation variances.  Use
     * {@link #homoscedasticT(StatisticalSummary, StatisticalSummary)} to
     * compute a t-statistic under the equal variances assumption.
     * <p>
     * This statistic can be used to perform a two-sample t-test to compare
     * sample means.</p>
     * <p>
      * The returned  t-statistic is</p>
     * <p>
     * &nbsp;&nbsp; <code>  t = (m1 - m2) / sqrt(var1/n1 + var2/n2)</code>
     * </p><p>
     * where <strong><code>n1</code></strong> is the size of the first sample;
     * <strong><code> n2</code></strong> is the size of the second sample;
     * <strong><code> m1</code></strong> is the mean of the first sample;
     * <strong><code> m2</code></strong> is the mean of the second sample
     * <strong><code> var1</code></strong> is the variance of the first sample;
     * <strong><code> var2</code></strong> is the variance of the second sample
     * </p><p>
     * <strong>Preconditions</strong>: <ul>
     * <li>The datasets described by the two Univariates must each contain
     * at least 2 observations.
     * </li></ul></p>
     *
     * @param sampleStats1 StatisticalSummary describing data from the first sample
     * @param sampleStats2 StatisticalSummary describing data from the second sample
     * @return t statistic
     * @throws NullArgumentException if the sample statistics are <code>null</code>
     * @throws NumberIsTooSmallException if the number of samples is &lt; 2
     */
    public double t(final StatisticalSummary sampleStats1,
                    final StatisticalSummary sampleStats2)
        throws NullArgumentException, NumberIsTooSmallException {

        checkSampleData(sampleStats1);
        checkSampleData(sampleStats2);
        return t(sampleStats1.getMean(), sampleStats2.getMean(),
                 sampleStats1.getVariance(), sampleStats2.getVariance(),
                 sampleStats1.getN(), sampleStats2.getN());

    }

    /**
     * Computes a 2-sample t statistic, comparing the means of the datasets
     * described by two {@link StatisticalSummary} instances, under the
     * assumption of equal subpopulation variances.  To compute a t-statistic
     * without the equal variances assumption, use
     * {@link #t(StatisticalSummary, StatisticalSummary)}.
     * <p>
     * This statistic can be used to perform a (homoscedastic) two-sample
     * t-test to compare sample means.</p>
     * <p>
     * The t-statistic returned is</p>
     * <p>
     * &nbsp;&nbsp;<code>  t = (m1 - m2) / (sqrt(1/n1 +1/n2) sqrt(var))</code>
     * </p><p>
     * where <strong><code>n1</code></strong> is the size of first sample;
     * <strong><code> n2</code></strong> is the size of second sample;
     * <strong><code> m1</code></strong> is the mean of first sample;
     * <strong><code> m2</code></strong> is the mean of second sample
     * and <strong><code>var</code></strong> is the pooled variance estimate:
     * </p><p>
     * <code>var = sqrt(((n1 - 1)var1 + (n2 - 1)var2) / ((n1-1) + (n2-1)))</code>
     * </p><p>
     * with <strong><code>var1</code></strong> the variance of the first sample and
     * <strong><code>var2</code></strong> the variance of the second sample.
     * </p><p>
     * <strong>Preconditions</strong>: <ul>
     * <li>The datasets described by the two Univariates must each contain
     * at least 2 observations.
     * </li></ul></p>
     *
     * @param sampleStats1 StatisticalSummary describing data from the first sample
     * @param sampleStats2 StatisticalSummary describing data from the second sample
     * @return t statistic
     * @throws NullArgumentException if the sample statistics are <code>null</code>
     * @throws NumberIsTooSmallException if the number of samples is &lt; 2
     */
    public double homoscedasticT(final StatisticalSummary sampleStats1,
                                 final StatisticalSummary sampleStats2)
        throws NullArgumentException, NumberIsTooSmallException {

        checkSampleData(sampleStats1);
        checkSampleData(sampleStats2);
        return homoscedasticT(sampleStats1.getMean(), sampleStats2.getMean(),
                              sampleStats1.getVariance(), sampleStats2.getVariance(),
                              sampleStats1.getN(), sampleStats2.getN());

    }

    /**
     * Returns the <i>observed significance level</i>, or
     * <i>p-value</i>, associated with a one-sample, two-tailed t-test
     * comparing the mean of the input array with the constant <code>mu</code>.
     * <p>
     * The number returned is the smallest significance level
     * at which one can reject the null hypothesis that the mean equals
     * <code>mu</code> in favor of the two-sided alternative that the mean
     * is different from <code>mu</code>. For a one-sided test, divide the
     * returned value by 2.</p>
     * <p>
     * <strong>Usage Note:</strong><br>
     * The validity of the test depends on the assumptions of the parametric
     * t-test procedure, as discussed
     * <a href="http://www.basic.nwu.edu/statguidefiles/ttest_unpaired_ass_viol.html">here</a>
     * </p><p>
     * <strong>Preconditions</strong>: <ul>
     * <li>The observed array length must be at least 2.
     * </li></ul></p>
     *
     * @param mu constant value to compare sample mean against
     * @param sample array of sample data values
     * @return p-value
     * @throws NullArgumentException if the sample array is <code>null</code>
     * @throws NumberIsTooSmallException if the length of the array is &lt; 2
     * @throws MaxCountExceededException if an error occurs computing the p-value
     */
    public double tTest(final double mu, final double[] sample)
        throws NullArgumentException, NumberIsTooSmallException,
        MaxCountExceededException {

        checkSampleData(sample);
        // No try-catch or advertised exception because args have just been checked
        return tTest(StatUtils.mean(sample), mu, StatUtils.variance(sample),
                     sample.length);

    }

    /**
     * Performs a <a href="http://www.itl.nist.gov/div898/handbook/eda/section3/eda353.htm">
     * two-sided t-test</a> evaluating the null hypothesis that the mean of the population from
     * which <code>sample</code> is drawn equals <code>mu</code>.
     * <p>
     * Returns <code>true</code> iff the null hypothesis can be
     * rejected with confidence <code>1 - alpha</code>.  To
     * perform a 1-sided test, use <code>alpha * 2</code></p>
     * <p>
     * <strong>Examples:</strong><br><ol>
     * <li>To test the (2-sided) hypothesis <code>sample mean = mu </code> at
     * the 95% level, use <br><code>tTest(mu, sample, 0.05) </code>
     * </li>
     * <li>To test the (one-sided) hypothesis <code> sample mean < mu </code>
     * at the 99% level, first verify that the measured sample mean is less
     * than <code>mu</code> and then use
     * <br><code>tTest(mu, sample, 0.02) </code>
     * </li></ol></p>
     * <p>
     * <strong>Usage Note:</strong><br>
     * The validity of the test depends on the assumptions of the one-sample
     * parametric t-test procedure, as discussed
     * <a href="http://www.basic.nwu.edu/statguidefiles/sg_glos.html#one-sample">here</a>
     * </p><p>
     * <strong>Preconditions</strong>: <ul>
     * <li>The observed array length must be at least 2.
     * </li></ul></p>
     *
     * @param mu constant value to compare sample mean against
     * @param sample array of sample data values
     * @param alpha significance level of the test
     * @return p-value
     * @throws NullArgumentException if the sample array is <code>null</code>
     * @throws NumberIsTooSmallException if the length of the array is &lt; 2
     * @throws OutOfRangeException if <code>alpha</code> is not in the range (0, 0.5]
     * @throws MaxCountExceededException if an error computing the p-value
     */
    public boolean tTest(final double mu, final double[] sample, final double alpha)
        throws NullArgumentException, NumberIsTooSmallException,
        OutOfRangeException, MaxCountExceededException {

        checkSignificanceLevel(alpha);
        return tTest(mu, sample) < alpha;

    }

    /**
     * Returns the <i>observed significance level</i>, or
     * <i>p-value</i>, associated with a one-sample, two-tailed t-test
     * comparing the mean of the dataset described by <code>sampleStats</code>
     * with the constant <code>mu</code>.
     * <p>
     * The number returned is the smallest significance level
     * at which one can reject the null hypothesis that the mean equals
     * <code>mu</code> in favor of the two-sided alternative that the mean
     * is different from <code>mu</code>. For a one-sided test, divide the
     * returned value by 2.</p>
     * <p>
     * <strong>Usage Note:</strong><br>
     * The validity of the test depends on the assumptions of the parametric
     * t-test procedure, as discussed
     * <a href="http://www.basic.nwu.edu/statguidefiles/ttest_unpaired_ass_viol.html">
     * here</a></p>
     * <p>
     * <strong>Preconditions</strong>: <ul>
     * <li>The sample must contain at least 2 observations.
     * </li></ul></p>
     *
     * @param mu constant value to compare sample mean against
     * @param sampleStats StatisticalSummary describing sample data
     * @return p-value
     * @throws NullArgumentException if <code>sampleStats</code> is <code>null</code>
     * @throws NumberIsTooSmallException if the number of samples is &lt; 2
     * @throws MaxCountExceededException if an error occurs computing the p-value
     */
    public double tTest(final double mu, final StatisticalSummary sampleStats)
        throws NullArgumentException, NumberIsTooSmallException,
        MaxCountExceededException {

        checkSampleData(sampleStats);
        return tTest(sampleStats.getMean(), mu, sampleStats.getVariance(),
                     sampleStats.getN());

    }

    /**
     * Performs a <a href="http://www.itl.nist.gov/div898/handbook/eda/section3/eda353.htm">
     * two-sided t-test</a> evaluating the null hypothesis that the mean of the
     * population from which the dataset described by <code>stats</code> is
     * drawn equals <code>mu</code>.
     * <p>
     * Returns <code>true</code> iff the null hypothesis can be rejected with
     * confidence <code>1 - alpha</code>.  To  perform a 1-sided test, use
     * <code>alpha * 2.</code></p>
     * <p>
     * <strong>Examples:</strong><br><ol>
     * <li>To test the (2-sided) hypothesis <code>sample mean = mu </code> at
     * the 95% level, use <br><code>tTest(mu, sampleStats, 0.05) </code>
     * </li>
     * <li>To test the (one-sided) hypothesis <code> sample mean < mu </code>
     * at the 99% level, first verify that the measured sample mean is less
     * than <code>mu</code> and then use
     * <br><code>tTest(mu, sampleStats, 0.02) </code>
     * </li></ol></p>
     * <p>
     * <strong>Usage Note:</strong><br>
     * The validity of the test depends on the assumptions of the one-sample
     * parametric t-test procedure, as discussed
     * <a href="http://www.basic.nwu.edu/statguidefiles/sg_glos.html#one-sample">here</a>
     * </p><p>
     * <strong>Preconditions</strong>: <ul>
     * <li>The sample must include at least 2 observations.
     * </li></ul></p>
     *
     * @param mu constant value to compare sample mean against
     * @param sampleStats StatisticalSummary describing sample data values
     * @param alpha significance level of the test
     * @return p-value
     * @throws NullArgumentException if <code>sampleStats</code> is <code>null</code>
     * @throws NumberIsTooSmallException if the number of samples is &lt; 2
     * @throws OutOfRangeException if <code>alpha</code> is not in the range (0, 0.5]
     * @throws MaxCountExceededException if an error occurs computing the p-value
     */
    public boolean tTest(final double mu, final StatisticalSummary sampleStats,
                         final double alpha)
    throws NullArgumentException, NumberIsTooSmallException,
    OutOfRangeException, MaxCountExceededException {

        checkSignificanceLevel(alpha);
        return tTest(mu, sampleStats) < alpha;

    }

    /**
     * Returns the <i>observed significance level</i>, or
     * <i>p-value</i>, associated with a two-sample, two-tailed t-test
     * comparing the means of the input arrays.
     * <p>
     * The number returned is the smallest significance level
     * at which one can reject the null hypothesis that the two means are
     * equal in favor of the two-sided alternative that they are different.
     * For a one-sided test, divide the returned value by 2.</p>
     * <p>
     * The test does not assume that the underlying popuation variances are
     * equal  and it uses approximated degrees of freedom computed from the
     * sample data to compute the p-value.  The t-statistic used is as defined in
     * {@link #t(double[], double[])} and the Welch-Satterthwaite approximation
     * to the degrees of freedom is used,
     * as described
     * <a href="http://www.itl.nist.gov/div898/handbook/prc/section3/prc31.htm">
     * here.</a>  To perform the test under the assumption of equal subpopulation
     * variances, use {@link #homoscedasticTTest(double[], double[])}.</p>
     * <p>
     * <strong>Usage Note:</strong><br>
     * The validity of the p-value depends on the assumptions of the parametric
     * t-test procedure, as discussed
     * <a href="http://www.basic.nwu.edu/statguidefiles/ttest_unpaired_ass_viol.html">
     * here</a></p>
     * <p>
     * <strong>Preconditions</strong>: <ul>
     * <li>The observed array lengths must both be at least 2.
     * </li></ul></p>
     *
     * @param sample1 array of sample data values
     * @param sample2 array of sample data values
     * @return p-value for t-test
     * @throws NullArgumentException if the arrays are <code>null</code>
     * @throws NumberIsTooSmallException if the length of the arrays is &lt; 2
     * @throws MaxCountExceededException if an error occurs computing the p-value
     */
    public double tTest(final double[] sample1, final double[] sample2)
        throws NullArgumentException, NumberIsTooSmallException,
        MaxCountExceededException {

        checkSampleData(sample1);
        checkSampleData(sample2);
        // No try-catch or advertised exception because args have just been checked
        return tTest(StatUtils.mean(sample1), StatUtils.mean(sample2),
                     StatUtils.variance(sample1), StatUtils.variance(sample2),
                     sample1.length, sample2.length);

    }

    /**
     * Returns the <i>observed significance level</i>, or
     * <i>p-value</i>, associated with a two-sample, two-tailed t-test
     * comparing the means of the input arrays, under the assumption that
     * the two samples are drawn from subpopulations with equal variances.
     * To perform the test without the equal variances assumption, use
     * {@link #tTest(double[], double[])}.</p>
     * <p>
     * The number returned is the smallest significance level
     * at which one can reject the null hypothesis that the two means are
     * equal in favor of the two-sided alternative that they are different.
     * For a one-sided test, divide the returned value by 2.</p>
     * <p>
     * A pooled variance estimate is used to compute the t-statistic.  See
     * {@link #homoscedasticT(double[], double[])}. The sum of the sample sizes
     * minus 2 is used as the degrees of freedom.</p>
     * <p>
     * <strong>Usage Note:</strong><br>
     * The validity of the p-value depends on the assumptions of the parametric
     * t-test procedure, as discussed
     * <a href="http://www.basic.nwu.edu/statguidefiles/ttest_unpaired_ass_viol.html">
     * here</a></p>
     * <p>
     * <strong>Preconditions</strong>: <ul>
     * <li>The observed array lengths must both be at least 2.
     * </li></ul></p>
     *
     * @param sample1 array of sample data values
     * @param sample2 array of sample data values
     * @return p-value for t-test
     * @throws NullArgumentException if the arrays are <code>null</code>
     * @throws NumberIsTooSmallException if the length of the arrays is &lt; 2
     * @throws MaxCountExceededException if an error occurs computing the p-value
     */
    public double homoscedasticTTest(final double[] sample1, final double[] sample2)
        throws NullArgumentException, NumberIsTooSmallException,
        MaxCountExceededException {

        checkSampleData(sample1);
        checkSampleData(sample2);
        // No try-catch or advertised exception because args have just been checked
        return homoscedasticTTest(StatUtils.mean(sample1),
                                  StatUtils.mean(sample2),
                                  StatUtils.variance(sample1),
                                  StatUtils.variance(sample2),
                                  sample1.length, sample2.length);

    }

    /**
     * Performs a
     * <a href="http://www.itl.nist.gov/div898/handbook/eda/section3/eda353.htm">
     * two-sided t-test</a> evaluating the null hypothesis that <code>sample1</code>
     * and <code>sample2</code> are drawn from populations with the same mean,
     * with significance level <code>alpha</code>.  This test does not assume
     * that the subpopulation variances are equal.  To perform the test assuming
     * equal variances, use
     * {@link #homoscedasticTTest(double[], double[], double)}.
     * <p>
     * Returns <code>true</code> iff the null hypothesis that the means are
     * equal can be rejected with confidence <code>1 - alpha</code>.  To
     * perform a 1-sided test, use <code>alpha * 2</code></p>
     * <p>
     * See {@link #t(double[], double[])} for the formula used to compute the
     * t-statistic.  Degrees of freedom are approximated using the
     * <a href="http://www.itl.nist.gov/div898/handbook/prc/section3/prc31.htm">
     * Welch-Satterthwaite approximation.</a></p>
     * <p>
     * <strong>Examples:</strong><br><ol>
     * <li>To test the (2-sided) hypothesis <code>mean 1 = mean 2 </code> at
     * the 95% level,  use
     * <br><code>tTest(sample1, sample2, 0.05). </code>
     * </li>
     * <li>To test the (one-sided) hypothesis <code> mean 1 < mean 2 </code>,
     * at the 99% level, first verify that the measured  mean of <code>sample 1</code>
     * is less than the mean of <code>sample 2</code> and then use
     * <br><code>tTest(sample1, sample2, 0.02) </code>
     * </li></ol></p>
     * <p>
     * <strong>Usage Note:</strong><br>
     * The validity of the test depends on the assumptions of the parametric
     * t-test procedure, as discussed
     * <a href="http://www.basic.nwu.edu/statguidefiles/ttest_unpaired_ass_viol.html">
     * here</a></p>
     * <p>
     * <strong>Preconditions</strong>: <ul>
     * <li>The observed array lengths must both be at least 2.
     * </li>
     * <li> <code> 0 < alpha < 0.5 </code>
     * </li></ul></p>
     *
     * @param sample1 array of sample data values
     * @param sample2 array of sample data values
     * @param alpha significance level of the test
     * @return true if the null hypothesis can be rejected with
     * confidence 1 - alpha
     * @throws NullArgumentException if the arrays are <code>null</code>
     * @throws NumberIsTooSmallException if the length of the arrays is &lt; 2
     * @throws OutOfRangeException if <code>alpha</code> is not in the range (0, 0.5]
     * @throws MaxCountExceededException if an error occurs computing the p-value
     */
    public boolean tTest(final double[] sample1, final double[] sample2,
                         final double alpha)
        throws NullArgumentException, NumberIsTooSmallException,
        OutOfRangeException, MaxCountExceededException {

        checkSignificanceLevel(alpha);
        return tTest(sample1, sample2) < alpha;

    }

    /**
     * Performs a
     * <a href="http://www.itl.nist.gov/div898/handbook/eda/section3/eda353.htm">
     * two-sided t-test</a> evaluating the null hypothesis that <code>sample1</code>
     * and <code>sample2</code> are drawn from populations with the same mean,
     * with significance level <code>alpha</code>,  assuming that the
     * subpopulation variances are equal.  Use
     * {@link #tTest(double[], double[], double)} to perform the test without
     * the assumption of equal variances.
     * <p>
     * Returns <code>true</code> iff the null hypothesis that the means are
     * equal can be rejected with confidence <code>1 - alpha</code>.  To
     * perform a 1-sided test, use <code>alpha * 2.</code>  To perform the test
     * without the assumption of equal subpopulation variances, use
     * {@link #tTest(double[], double[], double)}.</p>
     * <p>
     * A pooled variance estimate is used to compute the t-statistic. See
     * {@link #t(double[], double[])} for the formula. The sum of the sample
     * sizes minus 2 is used as the degrees of freedom.</p>
     * <p>
     * <strong>Examples:</strong><br><ol>
     * <li>To test the (2-sided) hypothesis <code>mean 1 = mean 2 </code> at
     * the 95% level, use <br><code>tTest(sample1, sample2, 0.05). </code>
     * </li>
     * <li>To test the (one-sided) hypothesis <code> mean 1 < mean 2, </code>
     * at the 99% level, first verify that the measured mean of
     * <code>sample 1</code> is less than the mean of <code>sample 2</code>
     * and then use
     * <br><code>tTest(sample1, sample2, 0.02) </code>
     * </li></ol></p>
     * <p>
     * <strong>Usage Note:</strong><br>
     * The validity of the test depends on the assumptions of the parametric
     * t-test procedure, as discussed
     * <a href="http://www.basic.nwu.edu/statguidefiles/ttest_unpaired_ass_viol.html">
     * here</a></p>
     * <p>
     * <strong>Preconditions</strong>: <ul>
     * <li>The observed array lengths must both be at least 2.
     * </li>
     * <li> <code> 0 < alpha < 0.5 </code>
     * </li></ul></p>
     *
     * @param sample1 array of sample data values
     * @param sample2 array of sample data values
     * @param alpha significance level of the test
     * @return true if the null hypothesis can be rejected with
     * confidence 1 - alpha
     * @throws NullArgumentException if the arrays are <code>null</code>
     * @throws NumberIsTooSmallException if the length of the arrays is &lt; 2
     * @throws OutOfRangeException if <code>alpha</code> is not in the range (0, 0.5]
     * @throws MaxCountExceededException if an error occurs computing the p-value
     */
    public boolean homoscedasticTTest(final double[] sample1, final double[] sample2,
                                      final double alpha)
        throws NullArgumentException, NumberIsTooSmallException,
        OutOfRangeException, MaxCountExceededException {

        checkSignificanceLevel(alpha);
        return homoscedasticTTest(sample1, sample2) < alpha;

    }

    /**
     * Returns the <i>observed significance level</i>, or
     * <i>p-value</i>, associated with a two-sample, two-tailed t-test
     * comparing the means of the datasets described by two StatisticalSummary
     * instances.
     * <p>
     * The number returned is the smallest significance level
     * at which one can reject the null hypothesis that the two means are
     * equal in favor of the two-sided alternative that they are different.
     * For a one-sided test, divide the returned value by 2.</p>
     * <p>
     * The test does not assume that the underlying population variances are
     * equal  and it uses approximated degrees of freedom computed from the
     * sample data to compute the p-value.   To perform the test assuming
     * equal variances, use
     * {@link #homoscedasticTTest(StatisticalSummary, StatisticalSummary)}.</p>
     * <p>
     * <strong>Usage Note:</strong><br>
     * The validity of the p-value depends on the assumptions of the parametric
     * t-test procedure, as discussed
     * <a href="http://www.basic.nwu.edu/statguidefiles/ttest_unpaired_ass_viol.html">
     * here</a></p>
     * <p>
     * <strong>Preconditions</strong>: <ul>
     * <li>The datasets described by the two Univariates must each contain
     * at least 2 observations.
     * </li></ul></p>
     *
     * @param sampleStats1  StatisticalSummary describing data from the first sample
     * @param sampleStats2  StatisticalSummary describing data from the second sample
     * @return p-value for t-test
     * @throws NullArgumentException if the sample statistics are <code>null</code>
     * @throws NumberIsTooSmallException if the number of samples is &lt; 2
     * @throws MaxCountExceededException if an error occurs computing the p-value
     */
    public double tTest(final StatisticalSummary sampleStats1,
                        final StatisticalSummary sampleStats2)
        throws NullArgumentException, NumberIsTooSmallException,
        MaxCountExceededException {

        checkSampleData(sampleStats1);
        checkSampleData(sampleStats2);
        return tTest(sampleStats1.getMean(), sampleStats2.getMean(),
                     sampleStats1.getVariance(), sampleStats2.getVariance(),
                     sampleStats1.getN(), sampleStats2.getN());

    }

    /**
     * Returns the <i>observed significance level</i>, or
     * <i>p-value</i>, associated with a two-sample, two-tailed t-test
     * comparing the means of the datasets described by two StatisticalSummary
     * instances, under the hypothesis of equal subpopulation variances. To
     * perform a test without the equal variances assumption, use
     * {@link #tTest(StatisticalSummary, StatisticalSummary)}.
     * <p>
     * The number returned is the smallest significance level
     * at which one can reject the null hypothesis that the two means are
     * equal in favor of the two-sided alternative that they are different.
     * For a one-sided test, divide the returned value by 2.</p>
     * <p>
     * See {@link #homoscedasticT(double[], double[])} for the formula used to
     * compute the t-statistic. The sum of the  sample sizes minus 2 is used as
     * the degrees of freedom.</p>
     * <p>
     * <strong>Usage Note:</strong><br>
     * The validity of the p-value depends on the assumptions of the parametric
     * t-test procedure, as discussed
     * <a href="http://www.basic.nwu.edu/statguidefiles/ttest_unpaired_ass_viol.html">here</a>
     * </p><p>
     * <strong>Preconditions</strong>: <ul>
     * <li>The datasets described by the two Univariates must each contain
     * at least 2 observations.
     * </li></ul></p>
     *
     * @param sampleStats1  StatisticalSummary describing data from the first sample
     * @param sampleStats2  StatisticalSummary describing data from the second sample
     * @return p-value for t-test
     * @throws NullArgumentException if the sample statistics are <code>null</code>
     * @throws NumberIsTooSmallException if the number of samples is &lt; 2
     * @throws MaxCountExceededException if an error occurs computing the p-value
     */
    public double homoscedasticTTest(final StatisticalSummary sampleStats1,
                                     final StatisticalSummary sampleStats2)
        throws NullArgumentException, NumberIsTooSmallException,
        MaxCountExceededException {

        checkSampleData(sampleStats1);
        checkSampleData(sampleStats2);
        return homoscedasticTTest(sampleStats1.getMean(),
                                  sampleStats2.getMean(),
                                  sampleStats1.getVariance(),
                                  sampleStats2.getVariance(),
                                  sampleStats1.getN(), sampleStats2.getN());

    }

    /**
     * Performs a
     * <a href="http://www.itl.nist.gov/div898/handbook/eda/section3/eda353.htm">
     * two-sided t-test</a> evaluating the null hypothesis that
     * <code>sampleStats1</code> and <code>sampleStats2</code> describe
     * datasets drawn from populations with the same mean, with significance
     * level <code>alpha</code>.   This test does not assume that the
     * subpopulation variances are equal.  To perform the test under the equal
     * variances assumption, use
     * {@link #homoscedasticTTest(StatisticalSummary, StatisticalSummary)}.
     * <p>
     * Returns <code>true</code> iff the null hypothesis that the means are
     * equal can be rejected with confidence <code>1 - alpha</code>.  To
     * perform a 1-sided test, use <code>alpha * 2</code></p>
     * <p>
     * See {@link #t(double[], double[])} for the formula used to compute the
     * t-statistic.  Degrees of freedom are approximated using the
     * <a href="http://www.itl.nist.gov/div898/handbook/prc/section3/prc31.htm">
     * Welch-Satterthwaite approximation.</a></p>
     * <p>
     * <strong>Examples:</strong><br><ol>
     * <li>To test the (2-sided) hypothesis <code>mean 1 = mean 2 </code> at
     * the 95%, use
     * <br><code>tTest(sampleStats1, sampleStats2, 0.05) </code>
     * </li>
     * <li>To test the (one-sided) hypothesis <code> mean 1 < mean 2 </code>
     * at the 99% level,  first verify that the measured mean of
     * <code>sample 1</code> is less than  the mean of <code>sample 2</code>
     * and then use
     * <br><code>tTest(sampleStats1, sampleStats2, 0.02) </code>
     * </li></ol></p>
     * <p>
     * <strong>Usage Note:</strong><br>
     * The validity of the test depends on the assumptions of the parametric
     * t-test procedure, as discussed
     * <a href="http://www.basic.nwu.edu/statguidefiles/ttest_unpaired_ass_viol.html">
     * here</a></p>
     * <p>
     * <strong>Preconditions</strong>: <ul>
     * <li>The datasets described by the two Univariates must each contain
     * at least 2 observations.
     * </li>
     * <li> <code> 0 < alpha < 0.5 </code>
     * </li></ul></p>
     *
     * @param sampleStats1 StatisticalSummary describing sample data values
     * @param sampleStats2 StatisticalSummary describing sample data values
     * @param alpha significance level of the test
     * @return true if the null hypothesis can be rejected with
     * confidence 1 - alpha
     * @throws NullArgumentException if the sample statistics are <code>null</code>
     * @throws NumberIsTooSmallException if the number of samples is &lt; 2
     * @throws OutOfRangeException if <code>alpha</code> is not in the range (0, 0.5]
     * @throws MaxCountExceededException if an error occurs computing the p-value
     */
    public boolean tTest(final StatisticalSummary sampleStats1,
                         final StatisticalSummary sampleStats2,
                         final double alpha)
        throws NullArgumentException, NumberIsTooSmallException,
        OutOfRangeException, MaxCountExceededException {

        checkSignificanceLevel(alpha);
        return tTest(sampleStats1, sampleStats2) < alpha;

    }

    //----------------------------------------------- Protected methods

    /**
     * Computes approximate degrees of freedom for 2-sample t-test.
     *
     * @param v1 first sample variance
     * @param v2 second sample variance
     * @param n1 first sample n
     * @param n2 second sample n
     * @return approximate degrees of freedom
     */
    protected double df(double v1, double v2, double n1, double n2) {
        return (((v1 / n1) + (v2 / n2)) * ((v1 / n1) + (v2 / n2))) /
        ((v1 * v1) / (n1 * n1 * (n1 - 1d)) + (v2 * v2) /
                (n2 * n2 * (n2 - 1d)));
    }

    /**
     * Computes t test statistic for 1-sample t-test.
     *
     * @param m sample mean
     * @param mu constant to test against
     * @param v sample variance
     * @param n sample n
     * @return t test statistic
     */
    protected double t(final double m, final double mu,
                       final double v, final double n) {
        return (m - mu) / FastMath.sqrt(v / n);
    }

    /**
     * Computes t test statistic for 2-sample t-test.
     * <p>
     * Does not assume that subpopulation variances are equal.</p>
     *
     * @param m1 first sample mean
     * @param m2 second sample mean
     * @param v1 first sample variance
     * @param v2 second sample variance
     * @param n1 first sample n
     * @param n2 second sample n
     * @return t test statistic
     */
    protected double t(final double m1, final double m2,
                       final double v1, final double v2,
                       final double n1, final double n2)  {
        return (m1 - m2) / FastMath.sqrt((v1 / n1) + (v2 / n2));
    }

    /**
     * Computes t test statistic for 2-sample t-test under the hypothesis
     * of equal subpopulation variances.
     *
     * @param m1 first sample mean
     * @param m2 second sample mean
     * @param v1 first sample variance
     * @param v2 second sample variance
     * @param n1 first sample n
     * @param n2 second sample n
     * @return t test statistic
     */
    protected double homoscedasticT(final double m1, final double m2,
                                    final double v1, final double v2,
                                    final double n1, final double n2)  {
        final double pooledVariance = ((n1  - 1) * v1 + (n2 -1) * v2 ) / (n1 + n2 - 2);
        return (m1 - m2) / FastMath.sqrt(pooledVariance * (1d / n1 + 1d / n2));
    }

    /**
     * Computes p-value for 2-sided, 1-sample t-test.
     *
     * @param m sample mean
     * @param mu constant to test against
     * @param v sample variance
     * @param n sample n
     * @return p-value
     * @throws MaxCountExceededException if an error occurs computing the p-value
     * @throws MathIllegalArgumentException if n is not greater than 1
     */
    protected double tTest(final double m, final double mu,
                           final double v, final double n)
        throws MaxCountExceededException, MathIllegalArgumentException {

        final double t = FastMath.abs(t(m, mu, v, n));
        // pass a null rng to avoid unneeded overhead as we will not sample from this distribution
        final TDistribution distribution = new TDistribution(null, n - 1);
        return 2.0 * distribution.cumulativeProbability(-t);

    }

    /**
     * Computes p-value for 2-sided, 2-sample t-test.
     * <p>
     * Does not assume subpopulation variances are equal. Degrees of freedom
     * are estimated from the data.</p>
     *
     * @param m1 first sample mean
     * @param m2 second sample mean
     * @param v1 first sample variance
     * @param v2 second sample variance
     * @param n1 first sample n
     * @param n2 second sample n
     * @return p-value
     * @throws MaxCountExceededException if an error occurs computing the p-value
     * @throws NotStrictlyPositiveException if the estimated degrees of freedom is not
     * strictly positive
     */
    protected double tTest(final double m1, final double m2,
                           final double v1, final double v2,
                           final double n1, final double n2)
        throws MaxCountExceededException, NotStrictlyPositiveException {

        final double t = FastMath.abs(t(m1, m2, v1, v2, n1, n2));
        final double degreesOfFreedom = df(v1, v2, n1, n2);
        // pass a null rng to avoid unneeded overhead as we will not sample from this distribution
        final TDistribution distribution = new TDistribution(null, degreesOfFreedom);
        return 2.0 * distribution.cumulativeProbability(-t);

    }

    /**
     * Computes p-value for 2-sided, 2-sample t-test, under the assumption
     * of equal subpopulation variances.
     * <p>
     * The sum of the sample sizes minus 2 is used as degrees of freedom.</p>
     *
     * @param m1 first sample mean
     * @param m2 second sample mean
     * @param v1 first sample variance
     * @param v2 second sample variance
     * @param n1 first sample n
     * @param n2 second sample n
     * @return p-value
     * @throws MaxCountExceededException if an error occurs computing the p-value
     * @throws NotStrictlyPositiveException if the estimated degrees of freedom is not
     * strictly positive
     */
    protected double homoscedasticTTest(double m1, double m2,
                                        double v1, double v2,
                                        double n1, double n2)
        throws MaxCountExceededException, NotStrictlyPositiveException {

        final double t = FastMath.abs(homoscedasticT(m1, m2, v1, v2, n1, n2));
        final double degreesOfFreedom = n1 + n2 - 2;
        // pass a null rng to avoid unneeded overhead as we will not sample from this distribution
        final TDistribution distribution = new TDistribution(null, degreesOfFreedom);
        return 2.0 * distribution.cumulativeProbability(-t);

    }

    /**
     * Check significance level.
     *
     * @param alpha significance level
     * @throws OutOfRangeException if the significance level is out of bounds.
     */
    private void checkSignificanceLevel(final double alpha)
        throws OutOfRangeException {

        if (alpha <= 0 || alpha > 0.5) {
            throw new OutOfRangeException(LocalizedFormats.SIGNIFICANCE_LEVEL,
                                          alpha, 0.0, 0.5);
        }

    }

    /**
     * Check sample data.
     *
     * @param data Sample data.
     * @throws NullArgumentException if {@code data} is {@code null}.
     * @throws NumberIsTooSmallException if there is not enough sample data.
     */
    private void checkSampleData(final double[] data)
        throws NullArgumentException, NumberIsTooSmallException {

        if (data == null) {
            throw new NullArgumentException();
        }
        if (data.length < 2) {
            throw new NumberIsTooSmallException(
                    LocalizedFormats.INSUFFICIENT_DATA_FOR_T_STATISTIC,
                    data.length, 2, true);
        }

    }

    /**
     * Check sample data.
     *
     * @param stat Statistical summary.
     * @throws NullArgumentException if {@code data} is {@code null}.
     * @throws NumberIsTooSmallException if there is not enough sample data.
     */
    private void checkSampleData(final StatisticalSummary stat)
        throws NullArgumentException, NumberIsTooSmallException {

        if (stat == null) {
            throw new NullArgumentException();
        }
        if (stat.getN() < 2) {
            throw new NumberIsTooSmallException(
                    LocalizedFormats.INSUFFICIENT_DATA_FOR_T_STATISTIC,
                    stat.getN(), 2, true);
        }

    }

}
