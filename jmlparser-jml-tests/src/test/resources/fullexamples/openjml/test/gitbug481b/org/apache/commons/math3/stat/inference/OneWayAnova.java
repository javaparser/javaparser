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

import java.util.ArrayList;
import java.util.Collection;

import org.apache.commons.math3.distribution.FDistribution;
import org.apache.commons.math3.exception.ConvergenceException;
import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.MaxCountExceededException;
import org.apache.commons.math3.exception.NullArgumentException;
import org.apache.commons.math3.exception.OutOfRangeException;
import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.stat.descriptive.SummaryStatistics;
import org.apache.commons.math3.util.MathUtils;

/**
 * Implements one-way ANOVA (analysis of variance) statistics.
 *
 * <p> Tests for differences between two or more categories of univariate data
 * (for example, the body mass index of accountants, lawyers, doctors and
 * computer programmers).  When two categories are given, this is equivalent to
 * the {@link org.apache.commons.math3.stat.inference.TTest}.
 * </p><p>
 * Uses the {@link org.apache.commons.math3.distribution.FDistribution
 * commons-math F Distribution implementation} to estimate exact p-values.</p>
 * <p>This implementation is based on a description at
 * http://faculty.vassar.edu/lowry/ch13pt1.html</p>
 * <pre>
 * Abbreviations: bg = between groups,
 *                wg = within groups,
 *                ss = sum squared deviations
 * </pre>
 *
 * @since 1.2
 */
public class OneWayAnova {

    /**
     * Default constructor.
     */
    public OneWayAnova() {
    }

    /**
     * Computes the ANOVA F-value for a collection of <code>double[]</code>
     * arrays.
     *
     * <p><strong>Preconditions</strong>: <ul>
     * <li>The categoryData <code>Collection</code> must contain
     * <code>double[]</code> arrays.</li>
     * <li> There must be at least two <code>double[]</code> arrays in the
     * <code>categoryData</code> collection and each of these arrays must
     * contain at least two values.</li></ul></p><p>
     * This implementation computes the F statistic using the definitional
     * formula<pre>
     *   F = msbg/mswg</pre>
     * where<pre>
     *  msbg = between group mean square
     *  mswg = within group mean square</pre>
     * are as defined <a href="http://faculty.vassar.edu/lowry/ch13pt1.html">
     * here</a></p>
     *
     * @param categoryData <code>Collection</code> of <code>double[]</code>
     * arrays each containing data for one category
     * @return Fvalue
     * @throws NullArgumentException if <code>categoryData</code> is <code>null</code>
     * @throws DimensionMismatchException if the length of the <code>categoryData</code>
     * array is less than 2 or a contained <code>double[]</code> array does not have
     * at least two values
     */
    public double anovaFValue(final Collection<double[]> categoryData)
        throws NullArgumentException, DimensionMismatchException {

        AnovaStats a = anovaStats(categoryData);
        return a.F;

    }

    /**
     * Computes the ANOVA P-value for a collection of <code>double[]</code>
     * arrays.
     *
     * <p><strong>Preconditions</strong>: <ul>
     * <li>The categoryData <code>Collection</code> must contain
     * <code>double[]</code> arrays.</li>
     * <li> There must be at least two <code>double[]</code> arrays in the
     * <code>categoryData</code> collection and each of these arrays must
     * contain at least two values.</li></ul></p><p>
     * This implementation uses the
     * {@link org.apache.commons.math3.distribution.FDistribution
     * commons-math F Distribution implementation} to estimate the exact
     * p-value, using the formula<pre>
     *   p = 1 - cumulativeProbability(F)</pre>
     * where <code>F</code> is the F value and <code>cumulativeProbability</code>
     * is the commons-math implementation of the F distribution.</p>
     *
     * @param categoryData <code>Collection</code> of <code>double[]</code>
     * arrays each containing data for one category
     * @return Pvalue
     * @throws NullArgumentException if <code>categoryData</code> is <code>null</code>
     * @throws DimensionMismatchException if the length of the <code>categoryData</code>
     * array is less than 2 or a contained <code>double[]</code> array does not have
     * at least two values
     * @throws ConvergenceException if the p-value can not be computed due to a convergence error
     * @throws MaxCountExceededException if the maximum number of iterations is exceeded
     */
    public double anovaPValue(final Collection<double[]> categoryData)
        throws NullArgumentException, DimensionMismatchException,
        ConvergenceException, MaxCountExceededException {

        final AnovaStats a = anovaStats(categoryData);
        // No try-catch or advertised exception because args are valid
        // pass a null rng to avoid unneeded overhead as we will not sample from this distribution
        final FDistribution fdist = new FDistribution(null, a.dfbg, a.dfwg);
        return 1.0 - fdist.cumulativeProbability(a.F);

    }

    /**
     * Computes the ANOVA P-value for a collection of {@link SummaryStatistics}.
     *
     * <p><strong>Preconditions</strong>: <ul>
     * <li>The categoryData <code>Collection</code> must contain
     * {@link SummaryStatistics}.</li>
     * <li> There must be at least two {@link SummaryStatistics} in the
     * <code>categoryData</code> collection and each of these statistics must
     * contain at least two values.</li></ul></p><p>
     * This implementation uses the
     * {@link org.apache.commons.math3.distribution.FDistribution
     * commons-math F Distribution implementation} to estimate the exact
     * p-value, using the formula<pre>
     *   p = 1 - cumulativeProbability(F)</pre>
     * where <code>F</code> is the F value and <code>cumulativeProbability</code>
     * is the commons-math implementation of the F distribution.</p>
     *
     * @param categoryData <code>Collection</code> of {@link SummaryStatistics}
     * each containing data for one category
     * @param allowOneElementData if true, allow computation for one catagory
     * only or for one data element per category
     * @return Pvalue
     * @throws NullArgumentException if <code>categoryData</code> is <code>null</code>
     * @throws DimensionMismatchException if the length of the <code>categoryData</code>
     * array is less than 2 or a contained {@link SummaryStatistics} does not have
     * at least two values
     * @throws ConvergenceException if the p-value can not be computed due to a convergence error
     * @throws MaxCountExceededException if the maximum number of iterations is exceeded
     * @since 3.2
     */
    public double anovaPValue(final Collection<SummaryStatistics> categoryData,
                              final boolean allowOneElementData)
        throws NullArgumentException, DimensionMismatchException,
               ConvergenceException, MaxCountExceededException {

        final AnovaStats a = anovaStats(categoryData, allowOneElementData);
        // pass a null rng to avoid unneeded overhead as we will not sample from this distribution
        final FDistribution fdist = new FDistribution(null, a.dfbg, a.dfwg);
        return 1.0 - fdist.cumulativeProbability(a.F);

    }

    /**
     * This method calls the method that actually does the calculations (except
     * P-value).
     *
     * @param categoryData
     *            <code>Collection</code> of <code>double[]</code> arrays each
     *            containing data for one category
     * @return computed AnovaStats
     * @throws NullArgumentException
     *             if <code>categoryData</code> is <code>null</code>
     * @throws DimensionMismatchException
     *             if the length of the <code>categoryData</code> array is less
     *             than 2 or a contained <code>double[]</code> array does not
     *             contain at least two values
     */
    private AnovaStats anovaStats(final Collection<double[]> categoryData)
        throws NullArgumentException, DimensionMismatchException {

        MathUtils.checkNotNull(categoryData);

        final Collection<SummaryStatistics> categoryDataSummaryStatistics =
                new ArrayList<SummaryStatistics>(categoryData.size());

        // convert arrays to SummaryStatistics
        for (final double[] data : categoryData) {
            final SummaryStatistics dataSummaryStatistics = new SummaryStatistics();
            categoryDataSummaryStatistics.add(dataSummaryStatistics);
            for (final double val : data) {
                dataSummaryStatistics.addValue(val);
            }
        }

        return anovaStats(categoryDataSummaryStatistics, false);

    }

    /**
     * Performs an ANOVA test, evaluating the null hypothesis that there
     * is no difference among the means of the data categories.
     *
     * <p><strong>Preconditions</strong>: <ul>
     * <li>The categoryData <code>Collection</code> must contain
     * <code>double[]</code> arrays.</li>
     * <li> There must be at least two <code>double[]</code> arrays in the
     * <code>categoryData</code> collection and each of these arrays must
     * contain at least two values.</li>
     * <li>alpha must be strictly greater than 0 and less than or equal to 0.5.
     * </li></ul></p><p>
     * This implementation uses the
     * {@link org.apache.commons.math3.distribution.FDistribution
     * commons-math F Distribution implementation} to estimate the exact
     * p-value, using the formula<pre>
     *   p = 1 - cumulativeProbability(F)</pre>
     * where <code>F</code> is the F value and <code>cumulativeProbability</code>
     * is the commons-math implementation of the F distribution.</p>
     * <p>True is returned iff the estimated p-value is less than alpha.</p>
     *
     * @param categoryData <code>Collection</code> of <code>double[]</code>
     * arrays each containing data for one category
     * @param alpha significance level of the test
     * @return true if the null hypothesis can be rejected with
     * confidence 1 - alpha
     * @throws NullArgumentException if <code>categoryData</code> is <code>null</code>
     * @throws DimensionMismatchException if the length of the <code>categoryData</code>
     * array is less than 2 or a contained <code>double[]</code> array does not have
     * at least two values
     * @throws OutOfRangeException if <code>alpha</code> is not in the range (0, 0.5]
     * @throws ConvergenceException if the p-value can not be computed due to a convergence error
     * @throws MaxCountExceededException if the maximum number of iterations is exceeded
     */
    public boolean anovaTest(final Collection<double[]> categoryData,
                             final double alpha)
        throws NullArgumentException, DimensionMismatchException,
        OutOfRangeException, ConvergenceException, MaxCountExceededException {

        if ((alpha <= 0) || (alpha > 0.5)) {
            throw new OutOfRangeException(
                    LocalizedFormats.OUT_OF_BOUND_SIGNIFICANCE_LEVEL,
                    alpha, 0, 0.5);
        }
        return anovaPValue(categoryData) < alpha;

    }

    /**
     * This method actually does the calculations (except P-value).
     *
     * @param categoryData <code>Collection</code> of <code>double[]</code>
     * arrays each containing data for one category
     * @param allowOneElementData if true, allow computation for one catagory
     * only or for one data element per category
     * @return computed AnovaStats
     * @throws NullArgumentException if <code>categoryData</code> is <code>null</code>
     * @throws DimensionMismatchException if <code>allowOneElementData</code> is false and the number of
     * categories is less than 2 or a contained SummaryStatistics does not contain
     * at least two values
     */
    private AnovaStats anovaStats(final Collection<SummaryStatistics> categoryData,
                                  final boolean allowOneElementData)
        throws NullArgumentException, DimensionMismatchException {

        MathUtils.checkNotNull(categoryData);

        if (!allowOneElementData) {
            // check if we have enough categories
            if (categoryData.size() < 2) {
                throw new DimensionMismatchException(LocalizedFormats.TWO_OR_MORE_CATEGORIES_REQUIRED,
                                                     categoryData.size(), 2);
            }

            // check if each category has enough data
            for (final SummaryStatistics array : categoryData) {
                if (array.getN() <= 1) {
                    throw new DimensionMismatchException(LocalizedFormats.TWO_OR_MORE_VALUES_IN_CATEGORY_REQUIRED,
                                                         (int) array.getN(), 2);
                }
            }
        }

        int dfwg = 0;
        double sswg = 0;
        double totsum = 0;
        double totsumsq = 0;
        int totnum = 0;

        for (final SummaryStatistics data : categoryData) {

            final double sum = data.getSum();
            final double sumsq = data.getSumsq();
            final int num = (int) data.getN();
            totnum += num;
            totsum += sum;
            totsumsq += sumsq;

            dfwg += num - 1;
            final double ss = sumsq - ((sum * sum) / num);
            sswg += ss;
        }

        final double sst = totsumsq - ((totsum * totsum) / totnum);
        final double ssbg = sst - sswg;
        final int dfbg = categoryData.size() - 1;
        final double msbg = ssbg / dfbg;
        final double mswg = sswg / dfwg;
        final double F = msbg / mswg;

        return new AnovaStats(dfbg, dfwg, F);

    }

    /**
        Convenience class to pass dfbg,dfwg,F values around within OneWayAnova.
        No get/set methods provided.
    */
    private static class AnovaStats {

        /** Degrees of freedom in numerator (between groups). */
        private final int dfbg;

        /** Degrees of freedom in denominator (within groups). */
        private final int dfwg;

        /** Statistic. */
        private final double F;

        /**
         * Constructor
         * @param dfbg degrees of freedom in numerator (between groups)
         * @param dfwg degrees of freedom in denominator (within groups)
         * @param F statistic
         */
        private AnovaStats(int dfbg, int dfwg, double F) {
            this.dfbg = dfbg;
            this.dfwg = dfwg;
            this.F = F;
        }
    }

}
