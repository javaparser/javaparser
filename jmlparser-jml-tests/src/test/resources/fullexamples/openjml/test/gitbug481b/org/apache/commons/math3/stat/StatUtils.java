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
package org.apache.commons.math3.stat;

import java.util.List;

import org.apache.commons.math3.exception.MathIllegalArgumentException;
import org.apache.commons.math3.exception.NotPositiveException;
import org.apache.commons.math3.exception.NullArgumentException;
import org.apache.commons.math3.exception.NumberIsTooSmallException;
import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.NoDataException;
import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.stat.descriptive.DescriptiveStatistics;
import org.apache.commons.math3.stat.descriptive.UnivariateStatistic;
import org.apache.commons.math3.stat.descriptive.moment.GeometricMean;
import org.apache.commons.math3.stat.descriptive.moment.Mean;
import org.apache.commons.math3.stat.descriptive.moment.Variance;
import org.apache.commons.math3.stat.descriptive.rank.Max;
import org.apache.commons.math3.stat.descriptive.rank.Min;
import org.apache.commons.math3.stat.descriptive.rank.Percentile;
import org.apache.commons.math3.stat.descriptive.summary.Product;
import org.apache.commons.math3.stat.descriptive.summary.Sum;
import org.apache.commons.math3.stat.descriptive.summary.SumOfLogs;
import org.apache.commons.math3.stat.descriptive.summary.SumOfSquares;

/**
 * StatUtils provides static methods for computing statistics based on data
 * stored in double[] arrays.
 *
 */
public final class StatUtils {

    /** sum */
    private static final UnivariateStatistic SUM = new Sum();

    /** sumSq */
    private static final UnivariateStatistic SUM_OF_SQUARES = new SumOfSquares();

    /** prod */
    private static final UnivariateStatistic PRODUCT = new Product();

    /** sumLog */
    private static final UnivariateStatistic SUM_OF_LOGS = new SumOfLogs();

    /** min */
    private static final UnivariateStatistic MIN = new Min();

    /** max */
    private static final UnivariateStatistic MAX = new Max();

    /** mean */
    private static final UnivariateStatistic MEAN = new Mean();

    /** variance */
    private static final Variance VARIANCE = new Variance();

    /** percentile */
    private static final Percentile PERCENTILE = new Percentile();

    /** geometric mean */
    private static final GeometricMean GEOMETRIC_MEAN = new GeometricMean();

    /**
     * Private Constructor
     */
    private StatUtils() {
    }

    /**
     * Returns the sum of the values in the input array, or
     * <code>Double.NaN</code> if the array is empty.
     * <p>
     * Throws <code>IllegalArgumentException</code> if the input array
     * is null.</p>
     *
     * @param values  array of values to sum
     * @return the sum of the values or <code>Double.NaN</code> if the array
     * is empty
     * @throws MathIllegalArgumentException if the array is null
     */
    public static double sum(final double[] values)
    throws MathIllegalArgumentException {
        return SUM.evaluate(values);
    }

    /**
     * Returns the sum of the entries in the specified portion of
     * the input array, or <code>Double.NaN</code> if the designated subarray
     * is empty.
     * <p>
     * Throws <code>IllegalArgumentException</code> if the array is null.</p>
     *
     * @param values the input array
     * @param begin index of the first array element to include
     * @param length the number of elements to include
     * @return the sum of the values or Double.NaN if length = 0
     * @throws MathIllegalArgumentException if the array is null or the array index
     *  parameters are not valid
     */
    public static double sum(final double[] values, final int begin,
            final int length) throws MathIllegalArgumentException {
        return SUM.evaluate(values, begin, length);
    }

    /**
     * Returns the sum of the squares of the entries in the input array, or
     * <code>Double.NaN</code> if the array is empty.
     * <p>
     * Throws <code>IllegalArgumentException</code> if the array is null.</p>
     *
     * @param values  input array
     * @return the sum of the squared values or <code>Double.NaN</code> if the
     * array is empty
     * @throws MathIllegalArgumentException if the array is null
     */
    public static double sumSq(final double[] values) throws MathIllegalArgumentException {
        return SUM_OF_SQUARES.evaluate(values);
    }

    /**
     * Returns the sum of the squares of the entries in the specified portion of
     * the input array, or <code>Double.NaN</code> if the designated subarray
     * is empty.
     * <p>
     * Throws <code>IllegalArgumentException</code> if the array is null.</p>
     *
     * @param values the input array
     * @param begin index of the first array element to include
     * @param length the number of elements to include
     * @return the sum of the squares of the values or Double.NaN if length = 0
     * @throws MathIllegalArgumentException if the array is null or the array index
     * parameters are not valid
     */
    public static double sumSq(final double[] values, final int begin,
            final int length) throws MathIllegalArgumentException {
        return SUM_OF_SQUARES.evaluate(values, begin, length);
    }

    /**
     * Returns the product of the entries in the input array, or
     * <code>Double.NaN</code> if the array is empty.
     * <p>
     * Throws <code>IllegalArgumentException</code> if the array is null.</p>
     *
     * @param values the input array
     * @return the product of the values or Double.NaN if the array is empty
     * @throws MathIllegalArgumentException if the array is null
     */
    public static double product(final double[] values)
    throws MathIllegalArgumentException {
        return PRODUCT.evaluate(values);
    }

    /**
     * Returns the product of the entries in the specified portion of
     * the input array, or <code>Double.NaN</code> if the designated subarray
     * is empty.
     * <p>
     * Throws <code>IllegalArgumentException</code> if the array is null.</p>
     *
     * @param values the input array
     * @param begin index of the first array element to include
     * @param length the number of elements to include
     * @return the product of the values or Double.NaN if length = 0
     * @throws MathIllegalArgumentException if the array is null or the array index
     * parameters are not valid
     */
    public static double product(final double[] values, final int begin,
            final int length) throws MathIllegalArgumentException {
        return PRODUCT.evaluate(values, begin, length);
    }

    /**
     * Returns the sum of the natural logs of the entries in the input array, or
     * <code>Double.NaN</code> if the array is empty.
     * <p>
     * Throws <code>IllegalArgumentException</code> if the array is null.</p>
     * <p>
     * See {@link org.apache.commons.math3.stat.descriptive.summary.SumOfLogs}.
     * </p>
     *
     * @param values the input array
     * @return the sum of the natural logs of the values or Double.NaN if
     * the array is empty
     * @throws MathIllegalArgumentException if the array is null
     */
    public static double sumLog(final double[] values)
    throws MathIllegalArgumentException {
        return SUM_OF_LOGS.evaluate(values);
    }

    /**
     * Returns the sum of the natural logs of the entries in the specified portion of
     * the input array, or <code>Double.NaN</code> if the designated subarray
     * is empty.
     * <p>
     * Throws <code>IllegalArgumentException</code> if the array is null.</p>
     * <p>
     * See {@link org.apache.commons.math3.stat.descriptive.summary.SumOfLogs}.
     * </p>
     *
     * @param values the input array
     * @param begin index of the first array element to include
     * @param length the number of elements to include
     * @return the sum of the natural logs of the values or Double.NaN if
     * length = 0
     * @throws MathIllegalArgumentException if the array is null or the array index
     * parameters are not valid
     */
    public static double sumLog(final double[] values, final int begin,
            final int length) throws MathIllegalArgumentException {
        return SUM_OF_LOGS.evaluate(values, begin, length);
    }

    /**
     * Returns the arithmetic mean of the entries in the input array, or
     * <code>Double.NaN</code> if the array is empty.
     * <p>
     * Throws <code>IllegalArgumentException</code> if the array is null.</p>
     * <p>
     * See {@link org.apache.commons.math3.stat.descriptive.moment.Mean} for
     * details on the computing algorithm.</p>
     *
     * @param values the input array
     * @return the mean of the values or Double.NaN if the array is empty
     * @throws MathIllegalArgumentException if the array is null
     */
    public static double mean(final double[] values)
    throws MathIllegalArgumentException {
        return MEAN.evaluate(values);
    }

    /**
     * Returns the arithmetic mean of the entries in the specified portion of
     * the input array, or <code>Double.NaN</code> if the designated subarray
     * is empty.
     * <p>
     * Throws <code>IllegalArgumentException</code> if the array is null.</p>
     * <p>
     * See {@link org.apache.commons.math3.stat.descriptive.moment.Mean} for
     * details on the computing algorithm.</p>
     *
     * @param values the input array
     * @param begin index of the first array element to include
     * @param length the number of elements to include
     * @return the mean of the values or Double.NaN if length = 0
     * @throws MathIllegalArgumentException if the array is null or the array index
     * parameters are not valid
     */
    public static double mean(final double[] values, final int begin,
            final int length) throws MathIllegalArgumentException {
        return MEAN.evaluate(values, begin, length);
    }

    /**
     * Returns the geometric mean of the entries in the input array, or
     * <code>Double.NaN</code> if the array is empty.
     * <p>
     * Throws <code>IllegalArgumentException</code> if the array is null.</p>
     * <p>
     * See {@link org.apache.commons.math3.stat.descriptive.moment.GeometricMean}
     * for details on the computing algorithm.</p>
     *
     * @param values the input array
     * @return the geometric mean of the values or Double.NaN if the array is empty
     * @throws MathIllegalArgumentException if the array is null
     */
    public static double geometricMean(final double[] values)
    throws MathIllegalArgumentException {
        return GEOMETRIC_MEAN.evaluate(values);
    }

    /**
     * Returns the geometric mean of the entries in the specified portion of
     * the input array, or <code>Double.NaN</code> if the designated subarray
     * is empty.
     * <p>
     * Throws <code>IllegalArgumentException</code> if the array is null.</p>
     * <p>
     * See {@link org.apache.commons.math3.stat.descriptive.moment.GeometricMean}
     * for details on the computing algorithm.</p>
     *
     * @param values the input array
     * @param begin index of the first array element to include
     * @param length the number of elements to include
     * @return the geometric mean of the values or Double.NaN if length = 0
     * @throws MathIllegalArgumentException if the array is null or the array index
     * parameters are not valid
     */
    public static double geometricMean(final double[] values, final int begin,
            final int length) throws MathIllegalArgumentException {
        return GEOMETRIC_MEAN.evaluate(values, begin, length);
    }


    /**
     * Returns the variance of the entries in the input array, or
     * <code>Double.NaN</code> if the array is empty.
     *
     * <p>This method returns the bias-corrected sample variance (using {@code n - 1} in
     * the denominator).  Use {@link #populationVariance(double[])} for the non-bias-corrected
     * population variance.</p>
     * <p>
     * See {@link org.apache.commons.math3.stat.descriptive.moment.Variance} for
     * details on the computing algorithm.</p>
     * <p>
     * Returns 0 for a single-value (i.e. length = 1) sample.</p>
     * <p>
     * Throws <code>MathIllegalArgumentException</code> if the array is null.</p>
     *
     * @param values the input array
     * @return the variance of the values or Double.NaN if the array is empty
     * @throws MathIllegalArgumentException if the array is null
     */
    public static double variance(final double[] values) throws MathIllegalArgumentException {
        return VARIANCE.evaluate(values);
    }

    /**
     * Returns the variance of the entries in the specified portion of
     * the input array, or <code>Double.NaN</code> if the designated subarray
     * is empty.
     *
     * <p>This method returns the bias-corrected sample variance (using {@code n - 1} in
     * the denominator).  Use {@link #populationVariance(double[], int, int)} for the non-bias-corrected
     * population variance.</p>
     * <p>
     * See {@link org.apache.commons.math3.stat.descriptive.moment.Variance} for
     * details on the computing algorithm.</p>
     * <p>
     * Returns 0 for a single-value (i.e. length = 1) sample.</p>
     * <p>
     * Throws <code>MathIllegalArgumentException</code> if the array is null or the
     * array index parameters are not valid.</p>
     *
     * @param values the input array
     * @param begin index of the first array element to include
     * @param length the number of elements to include
     * @return the variance of the values or Double.NaN if length = 0
     * @throws MathIllegalArgumentException if the array is null or the array index
     *  parameters are not valid
     */
    public static double variance(final double[] values, final int begin,
            final int length) throws MathIllegalArgumentException {
        return VARIANCE.evaluate(values, begin, length);
    }

    /**
     * Returns the variance of the entries in the specified portion of
     * the input array, using the precomputed mean value.  Returns
     * <code>Double.NaN</code> if the designated subarray is empty.
     *
     * <p>This method returns the bias-corrected sample variance (using {@code n - 1} in
     * the denominator).  Use {@link #populationVariance(double[], double, int, int)} for the non-bias-corrected
     * population variance.</p>
     * <p>
     * See {@link org.apache.commons.math3.stat.descriptive.moment.Variance} for
     * details on the computing algorithm.</p>
     * <p>
     * The formula used assumes that the supplied mean value is the arithmetic
     * mean of the sample data, not a known population parameter.  This method
     * is supplied only to save computation when the mean has already been
     * computed.</p>
     * <p>
     * Returns 0 for a single-value (i.e. length = 1) sample.</p>
     * <p>
     * Throws <code>MathIllegalArgumentException</code> if the array is null or the
     * array index parameters are not valid.</p>
     *
     * @param values the input array
     * @param mean the precomputed mean value
     * @param begin index of the first array element to include
     * @param length the number of elements to include
     * @return the variance of the values or Double.NaN if length = 0
     * @throws MathIllegalArgumentException if the array is null or the array index
     *  parameters are not valid
     */
    public static double variance(final double[] values, final double mean,
            final int begin, final int length) throws MathIllegalArgumentException {
        return VARIANCE.evaluate(values, mean, begin, length);
    }

    /**
     * Returns the variance of the entries in the input array, using the
     * precomputed mean value.  Returns <code>Double.NaN</code> if the array
     * is empty.
     *
     * <p>This method returns the bias-corrected sample variance (using {@code n - 1} in
     * the denominator).  Use {@link #populationVariance(double[], double)} for the non-bias-corrected
     * population variance.</p>
     * <p>
     * See {@link org.apache.commons.math3.stat.descriptive.moment.Variance} for
     * details on the computing algorithm.</p>
     * <p>
     * The formula used assumes that the supplied mean value is the arithmetic
     * mean of the sample data, not a known population parameter.  This method
     * is supplied only to save computation when the mean has already been
     * computed.</p>
     * <p>
     * Returns 0 for a single-value (i.e. length = 1) sample.</p>
     * <p>
     * Throws <code>MathIllegalArgumentException</code> if the array is null.</p>
     *
     * @param values the input array
     * @param mean the precomputed mean value
     * @return the variance of the values or Double.NaN if the array is empty
     * @throws MathIllegalArgumentException if the array is null
     */
    public static double variance(final double[] values, final double mean)
    throws MathIllegalArgumentException {
        return VARIANCE.evaluate(values, mean);
    }

    /**
     * Returns the <a href="http://en.wikibooks.org/wiki/Statistics/Summary/Variance">
     * population variance</a> of the entries in the input array, or
     * <code>Double.NaN</code> if the array is empty.
     * <p>
     * See {@link org.apache.commons.math3.stat.descriptive.moment.Variance} for
     * details on the formula and computing algorithm.</p>
     * <p>
     * Returns 0 for a single-value (i.e. length = 1) sample.</p>
     * <p>
     * Throws <code>MathIllegalArgumentException</code> if the array is null.</p>
     *
     * @param values the input array
     * @return the population variance of the values or Double.NaN if the array is empty
     * @throws MathIllegalArgumentException if the array is null
     */
    public static double populationVariance(final double[] values)
    throws MathIllegalArgumentException {
        return new Variance(false).evaluate(values);
    }

    /**
     * Returns the <a href="http://en.wikibooks.org/wiki/Statistics/Summary/Variance">
     * population variance</a> of the entries in the specified portion of
     * the input array, or <code>Double.NaN</code> if the designated subarray
     * is empty.
     * <p>
     * See {@link org.apache.commons.math3.stat.descriptive.moment.Variance} for
     * details on the computing algorithm.</p>
     * <p>
     * Returns 0 for a single-value (i.e. length = 1) sample.</p>
     * <p>
     * Throws <code>MathIllegalArgumentException</code> if the array is null or the
     * array index parameters are not valid.</p>
     *
     * @param values the input array
     * @param begin index of the first array element to include
     * @param length the number of elements to include
     * @return the population variance of the values or Double.NaN if length = 0
     * @throws MathIllegalArgumentException if the array is null or the array index
     *  parameters are not valid
     */
    public static double populationVariance(final double[] values, final int begin,
            final int length) throws MathIllegalArgumentException {
        return new Variance(false).evaluate(values, begin, length);
    }

    /**
     * Returns the <a href="http://en.wikibooks.org/wiki/Statistics/Summary/Variance">
     * population variance</a> of the entries in the specified portion of
     * the input array, using the precomputed mean value.  Returns
     * <code>Double.NaN</code> if the designated subarray is empty.
     * <p>
     * See {@link org.apache.commons.math3.stat.descriptive.moment.Variance} for
     * details on the computing algorithm.</p>
     * <p>
     * The formula used assumes that the supplied mean value is the arithmetic
     * mean of the sample data, not a known population parameter.  This method
     * is supplied only to save computation when the mean has already been
     * computed.</p>
     * <p>
     * Returns 0 for a single-value (i.e. length = 1) sample.</p>
     * <p>
     * Throws <code>MathIllegalArgumentException</code> if the array is null or the
     * array index parameters are not valid.</p>
     *
     * @param values the input array
     * @param mean the precomputed mean value
     * @param begin index of the first array element to include
     * @param length the number of elements to include
     * @return the population variance of the values or Double.NaN if length = 0
     * @throws MathIllegalArgumentException if the array is null or the array index
     *  parameters are not valid
     */
    public static double populationVariance(final double[] values, final double mean,
            final int begin, final int length) throws MathIllegalArgumentException {
        return new Variance(false).evaluate(values, mean, begin, length);
    }

    /**
     * Returns the <a href="http://en.wikibooks.org/wiki/Statistics/Summary/Variance">
     * population variance</a> of the entries in the input array, using the
     * precomputed mean value.  Returns <code>Double.NaN</code> if the array
     * is empty.
     * <p>
     * See {@link org.apache.commons.math3.stat.descriptive.moment.Variance} for
     * details on the computing algorithm.</p>
     * <p>
     * The formula used assumes that the supplied mean value is the arithmetic
     * mean of the sample data, not a known population parameter.  This method
     * is supplied only to save computation when the mean has already been
     * computed.</p>
     * <p>
     * Returns 0 for a single-value (i.e. length = 1) sample.</p>
     * <p>
     * Throws <code>MathIllegalArgumentException</code> if the array is null.</p>
     *
     * @param values the input array
     * @param mean the precomputed mean value
     * @return the population variance of the values or Double.NaN if the array is empty
     * @throws MathIllegalArgumentException if the array is null
     */
    public static double populationVariance(final double[] values, final double mean)
    throws MathIllegalArgumentException {
        return new Variance(false).evaluate(values, mean);
    }

    /**
     * Returns the maximum of the entries in the input array, or
     * <code>Double.NaN</code> if the array is empty.
     * <p>
     * Throws <code>MathIllegalArgumentException</code> if the array is null.</p>
     * <p>
     * <ul>
     * <li>The result is <code>NaN</code> iff all values are <code>NaN</code>
     * (i.e. <code>NaN</code> values have no impact on the value of the statistic).</li>
     * <li>If any of the values equals <code>Double.POSITIVE_INFINITY</code>,
     * the result is <code>Double.POSITIVE_INFINITY.</code></li>
     * </ul></p>
     *
     * @param values the input array
     * @return the maximum of the values or Double.NaN if the array is empty
     * @throws MathIllegalArgumentException if the array is null
     */
    public static double max(final double[] values) throws MathIllegalArgumentException {
        return MAX.evaluate(values);
    }

    /**
     * Returns the maximum of the entries in the specified portion of
     * the input array, or <code>Double.NaN</code> if the designated subarray
     * is empty.
     * <p>
     * Throws <code>MathIllegalArgumentException</code> if the array is null or
     * the array index parameters are not valid.</p>
     * <p>
     * <ul>
     * <li>The result is <code>NaN</code> iff all values are <code>NaN</code>
     * (i.e. <code>NaN</code> values have no impact on the value of the statistic).</li>
     * <li>If any of the values equals <code>Double.POSITIVE_INFINITY</code>,
     * the result is <code>Double.POSITIVE_INFINITY.</code></li>
     * </ul></p>
     *
     * @param values the input array
     * @param begin index of the first array element to include
     * @param length the number of elements to include
     * @return the maximum of the values or Double.NaN if length = 0
     * @throws MathIllegalArgumentException if the array is null or the array index
     * parameters are not valid
     */
    public static double max(final double[] values, final int begin,
            final int length) throws MathIllegalArgumentException {
        return MAX.evaluate(values, begin, length);
    }

     /**
     * Returns the minimum of the entries in the input array, or
     * <code>Double.NaN</code> if the array is empty.
     * <p>
     * Throws <code>MathIllegalArgumentException</code> if the array is null.</p>
     * <p>
     * <ul>
     * <li>The result is <code>NaN</code> iff all values are <code>NaN</code>
     * (i.e. <code>NaN</code> values have no impact on the value of the statistic).</li>
     * <li>If any of the values equals <code>Double.NEGATIVE_INFINITY</code>,
     * the result is <code>Double.NEGATIVE_INFINITY.</code></li>
     * </ul> </p>
     *
     * @param values the input array
     * @return the minimum of the values or Double.NaN if the array is empty
     * @throws MathIllegalArgumentException if the array is null
     */
    public static double min(final double[] values) throws MathIllegalArgumentException {
        return MIN.evaluate(values);
    }

     /**
     * Returns the minimum of the entries in the specified portion of
     * the input array, or <code>Double.NaN</code> if the designated subarray
     * is empty.
     * <p>
     * Throws <code>MathIllegalArgumentException</code> if the array is null or
     * the array index parameters are not valid.</p>
     * <p>
     * <ul>
     * <li>The result is <code>NaN</code> iff all values are <code>NaN</code>
     * (i.e. <code>NaN</code> values have no impact on the value of the statistic).</li>
     * <li>If any of the values equals <code>Double.NEGATIVE_INFINITY</code>,
     * the result is <code>Double.NEGATIVE_INFINITY.</code></li>
     * </ul></p>
     *
     * @param values the input array
     * @param begin index of the first array element to include
     * @param length the number of elements to include
     * @return the minimum of the values or Double.NaN if length = 0
     * @throws MathIllegalArgumentException if the array is null or the array index
     * parameters are not valid
     */
    public static double min(final double[] values, final int begin,
            final int length) throws MathIllegalArgumentException {
        return MIN.evaluate(values, begin, length);
    }

    /**
     * Returns an estimate of the <code>p</code>th percentile of the values
     * in the <code>values</code> array.
     * <p>
     * <ul>
     * <li>Returns <code>Double.NaN</code> if <code>values</code> has length
     * <code>0</code></li></p>
     * <li>Returns (for any value of <code>p</code>) <code>values[0]</code>
     *  if <code>values</code> has length <code>1</code></li>
     * <li>Throws <code>IllegalArgumentException</code> if <code>values</code>
     * is null  or p is not a valid quantile value (p must be greater than 0
     * and less than or equal to 100)</li>
     * </ul></p>
     * <p>
     * See {@link org.apache.commons.math3.stat.descriptive.rank.Percentile} for
     * a description of the percentile estimation algorithm used.</p>
     *
     * @param values input array of values
     * @param p the percentile value to compute
     * @return the percentile value or Double.NaN if the array is empty
     * @throws MathIllegalArgumentException if <code>values</code> is null
     * or p is invalid
     */
    public static double percentile(final double[] values, final double p)
    throws MathIllegalArgumentException {
            return PERCENTILE.evaluate(values,p);
    }

     /**
     * Returns an estimate of the <code>p</code>th percentile of the values
     * in the <code>values</code> array, starting with the element in (0-based)
     * position <code>begin</code> in the array and including <code>length</code>
     * values.
     * <p>
     * <ul>
     * <li>Returns <code>Double.NaN</code> if <code>length = 0</code></li>
     * <li>Returns (for any value of <code>p</code>) <code>values[begin]</code>
     *  if <code>length = 1 </code></li>
     * <li>Throws <code>MathIllegalArgumentException</code> if <code>values</code>
     *  is null , <code>begin</code> or <code>length</code> is invalid, or
     * <code>p</code> is not a valid quantile value (p must be greater than 0
     * and less than or equal to 100)</li>
     * </ul></p>
     * <p>
     * See {@link org.apache.commons.math3.stat.descriptive.rank.Percentile} for
     * a description of the percentile estimation algorithm used.</p>
     *
     * @param values array of input values
     * @param p  the percentile to compute
     * @param begin  the first (0-based) element to include in the computation
     * @param length  the number of array elements to include
     * @return  the percentile value
     * @throws MathIllegalArgumentException if the parameters are not valid or the
     * input array is null
     */
    public static double percentile(final double[] values, final int begin,
            final int length, final double p) throws MathIllegalArgumentException {
        return PERCENTILE.evaluate(values, begin, length, p);
    }

    /**
     * Returns the sum of the (signed) differences between corresponding elements of the
     * input arrays -- i.e., sum(sample1[i] - sample2[i]).
     *
     * @param sample1  the first array
     * @param sample2  the second array
     * @return sum of paired differences
     * @throws DimensionMismatchException if the arrays do not have the same
     * (positive) length.
     * @throws NoDataException if the sample arrays are empty.
     */
    public static double sumDifference(final double[] sample1, final double[] sample2)
    throws DimensionMismatchException, NoDataException {
        int n = sample1.length;
        if (n != sample2.length) {
            throw new DimensionMismatchException(n, sample2.length);
        }
        if (n <= 0) {
            throw new NoDataException(LocalizedFormats.INSUFFICIENT_DIMENSION);
        }
        double result = 0;
        for (int i = 0; i < n; i++) {
            result += sample1[i] - sample2[i];
        }
        return result;
    }

    /**
     * Returns the mean of the (signed) differences between corresponding elements of the
     * input arrays -- i.e., sum(sample1[i] - sample2[i]) / sample1.length.
     *
     * @param sample1  the first array
     * @param sample2  the second array
     * @return mean of paired differences
     * @throws DimensionMismatchException if the arrays do not have the same
     * (positive) length.
     * @throws NoDataException if the sample arrays are empty.
     */
    public static double meanDifference(final double[] sample1, final double[] sample2)
    throws DimensionMismatchException, NoDataException{
        return sumDifference(sample1, sample2) / sample1.length;
    }

    /**
     * Returns the variance of the (signed) differences between corresponding elements of the
     * input arrays -- i.e., var(sample1[i] - sample2[i]).
     *
     * @param sample1  the first array
     * @param sample2  the second array
     * @param meanDifference   the mean difference between corresponding entries
     * @see #meanDifference(double[],double[])
     * @return variance of paired differences
     * @throws DimensionMismatchException if the arrays do not have the same
     * length.
     * @throws NumberIsTooSmallException if the arrays length is less than 2.
     */
    public static double varianceDifference(final double[] sample1,
            final double[] sample2, double meanDifference) throws DimensionMismatchException,
            NumberIsTooSmallException {
        double sum1 = 0d;
        double sum2 = 0d;
        double diff = 0d;
        int n = sample1.length;
        if (n != sample2.length) {
            throw new DimensionMismatchException(n, sample2.length);
        }
        if (n < 2) {
            throw new NumberIsTooSmallException(n, 2, true);
        }
        for (int i = 0; i < n; i++) {
            diff = sample1[i] - sample2[i];
            sum1 += (diff - meanDifference) *(diff - meanDifference);
            sum2 += diff - meanDifference;
        }
        return (sum1 - (sum2 * sum2 / n)) / (n - 1);
    }

    /**
     * Normalize (standardize) the sample, so it is has a mean of 0 and a standard deviation of 1.
     *
     * @param sample Sample to normalize.
     * @return normalized (standardized) sample.
     * @since 2.2
     */
    public static double[] normalize(final double[] sample) {
        DescriptiveStatistics stats = new DescriptiveStatistics();

        // Add the data from the series to stats
        for (int i = 0; i < sample.length; i++) {
            stats.addValue(sample[i]);
        }

        // Compute mean and standard deviation
        double mean = stats.getMean();
        double standardDeviation = stats.getStandardDeviation();

        // initialize the standardizedSample, which has the same length as the sample
        double[] standardizedSample = new double[sample.length];

        for (int i = 0; i < sample.length; i++) {
            // z = (x- mean)/standardDeviation
            standardizedSample[i] = (sample[i] - mean) / standardDeviation;
        }
        return standardizedSample;
    }

    /**
     * Returns the sample mode(s).  The mode is the most frequently occurring
     * value in the sample. If there is a unique value with maximum frequency,
     * this value is returned as the only element of the output array. Otherwise,
     * the returned array contains the maximum frequency elements in increasing
     * order.  For example, if {@code sample} is {0, 12, 5, 6, 0, 13, 5, 17},
     * the returned array will have length two, with 0 in the first element and
     * 5 in the second.
     *
     * <p>NaN values are ignored when computing the mode - i.e., NaNs will never
     * appear in the output array.  If the sample includes only NaNs or has
     * length 0, an empty array is returned.</p>
     *
     * @param sample input data
     * @return array of array of the most frequently occurring element(s) sorted in ascending order.
     * @throws MathIllegalArgumentException if the indices are invalid or the array is null
     * @since 3.3
     */
    public static double[] mode(double[] sample) throws MathIllegalArgumentException {
        if (sample == null) {
            throw new NullArgumentException(LocalizedFormats.INPUT_ARRAY);
        }
        return getMode(sample, 0, sample.length);
    }

    /**
     * Returns the sample mode(s).  The mode is the most frequently occurring
     * value in the sample. If there is a unique value with maximum frequency,
     * this value is returned as the only element of the output array. Otherwise,
     * the returned array contains the maximum frequency elements in increasing
     * order.  For example, if {@code sample} is {0, 12, 5, 6, 0, 13, 5, 17},
     * the returned array will have length two, with 0 in the first element and
     * 5 in the second.
     *
     * <p>NaN values are ignored when computing the mode - i.e., NaNs will never
     * appear in the output array.  If the sample includes only NaNs or has
     * length 0, an empty array is returned.</p>
     *
     * @param sample input data
     * @param begin index (0-based) of the first array element to include
     * @param length the number of elements to include
     *
     * @return array of array of the most frequently occurring element(s) sorted in ascending order.
     * @throws MathIllegalArgumentException if the indices are invalid or the array is null
     * @since 3.3
     */
    public static double[] mode(double[] sample, final int begin, final int length) {
        if (sample == null) {
            throw new NullArgumentException(LocalizedFormats.INPUT_ARRAY);
        }

        if (begin < 0) {
            throw new NotPositiveException(LocalizedFormats.START_POSITION, Integer.valueOf(begin));
        }

        if (length < 0) {
            throw new NotPositiveException(LocalizedFormats.LENGTH, Integer.valueOf(length));
        }

        return getMode(sample, begin, length);
    }

    /**
     * Private helper method.
     * Assumes parameters have been validated.
     * @param values input data
     * @param begin index (0-based) of the first array element to include
     * @param length the number of elements to include
     * @return array of array of the most frequently occurring element(s) sorted in ascending order.
     */
    private static double[] getMode(double[] values, final int begin, final int length) {
        // Add the values to the frequency table
        Frequency freq = new Frequency();
        for (int i = begin; i < begin + length; i++) {
            final double value = values[i];
            if (!Double.isNaN(value)) {
                freq.addValue(Double.valueOf(value));
            }
        }
        List<Comparable<?>> list = freq.getMode();
        // Convert the list to an array of primitive double
        double[] modes = new double[list.size()];
        int i = 0;
        for(Comparable<?> c : list) {
            modes[i++] = ((Double) c).doubleValue();
        }
        return modes;
    }

}
