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
package org.apache.commons.math3.stat.descriptive;

import org.apache.commons.math3.exception.NotPositiveException;
import org.apache.commons.math3.exception.NullArgumentException;
import org.apache.commons.math3.exception.NumberIsTooLargeException;
import org.apache.commons.math3.exception.MathIllegalArgumentException;
import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.util.MathArrays;

/**
 * Abstract base class for all implementations of the
 * {@link UnivariateStatistic} interface.
 * <p>
 * Provides a default implementation of <code>evaluate(double[]),</code>
 * delegating to <code>evaluate(double[], int, int)</code> in the natural way.
 * </p>
 * <p>
 * Also includes a <code>test</code> method that performs generic parameter
 * validation for the <code>evaluate</code> methods.</p>
 *
 */
public abstract class AbstractUnivariateStatistic
    implements UnivariateStatistic {

    /** Stored data. */
    private double[] storedData;

    /**
     * Set the data array.
     * <p>
     * The stored value is a copy of the parameter array, not the array itself.
     * </p>
     * @param values data array to store (may be null to remove stored data)
     * @see #evaluate()
     */
    public void setData(final double[] values) {
        storedData = (values == null) ? null : values.clone();
    }

    /**
     * Get a copy of the stored data array.
     * @return copy of the stored data array (may be null)
     */
    public double[] getData() {
        return (storedData == null) ? null : storedData.clone();
    }

    /**
     * Get a reference to the stored data array.
     * @return reference to the stored data array (may be null)
     */
    protected double[] getDataRef() {
        return storedData;
    }

    /**
     * Set the data array.  The input array is copied, not referenced.
     *
     * @param values data array to store
     * @param begin the index of the first element to include
     * @param length the number of elements to include
     * @throws MathIllegalArgumentException if values is null or the indices
     * are not valid
     * @see #evaluate()
     */
    public void setData(final double[] values, final int begin, final int length)
    throws MathIllegalArgumentException {
        if (values == null) {
            throw new NullArgumentException(LocalizedFormats.INPUT_ARRAY);
        }

        if (begin < 0) {
            throw new NotPositiveException(LocalizedFormats.START_POSITION, begin);
        }

        if (length < 0) {
            throw new NotPositiveException(LocalizedFormats.LENGTH, length);
        }

        if (begin + length > values.length) {
            throw new NumberIsTooLargeException(LocalizedFormats.SUBARRAY_ENDS_AFTER_ARRAY_END,
                                                begin + length, values.length, true);
        }
        storedData = new double[length];
        System.arraycopy(values, begin, storedData, 0, length);
    }

    /**
     * Returns the result of evaluating the statistic over the stored data.
     * <p>
     * The stored array is the one which was set by previous calls to {@link #setData(double[])}.
     * </p>
     * @return the value of the statistic applied to the stored data
     * @throws MathIllegalArgumentException if the stored data array is null
     */
    public double evaluate() throws MathIllegalArgumentException {
        return evaluate(storedData);
    }

    /**
     * {@inheritDoc}
     */
    public double evaluate(final double[] values) throws MathIllegalArgumentException {
        test(values, 0, 0);
        return evaluate(values, 0, values.length);
    }

    /**
     * {@inheritDoc}
     */
    public abstract double evaluate(final double[] values, final int begin, final int length)
    throws MathIllegalArgumentException;

    /**
     * {@inheritDoc}
     */
    public abstract UnivariateStatistic copy();

    /**
     * This method is used by <code>evaluate(double[], int, int)</code> methods
     * to verify that the input parameters designate a subarray of positive length.
     * <p>
     * <ul>
     * <li>returns <code>true</code> iff the parameters designate a subarray of
     * positive length</li>
     * <li>throws <code>MathIllegalArgumentException</code> if the array is null or
     * or the indices are invalid</li>
     * <li>returns <code>false</li> if the array is non-null, but
     * <code>length</code> is 0.
     * </ul></p>
     *
     * @param values the input array
     * @param begin index of the first array element to include
     * @param length the number of elements to include
     * @return true if the parameters are valid and designate a subarray of positive length
     * @throws MathIllegalArgumentException if the indices are invalid or the array is null
     */
    protected boolean test(
        final double[] values,
        final int begin,
        final int length) throws MathIllegalArgumentException {
        return MathArrays.verifyValues(values, begin, length, false);
    }

    /**
     * This method is used by <code>evaluate(double[], int, int)</code> methods
     * to verify that the input parameters designate a subarray of positive length.
     * <p>
     * <ul>
     * <li>returns <code>true</code> iff the parameters designate a subarray of
     * non-negative length</li>
     * <li>throws <code>IllegalArgumentException</code> if the array is null or
     * or the indices are invalid</li>
     * <li>returns <code>false</li> if the array is non-null, but
     * <code>length</code> is 0 unless <code>allowEmpty</code> is <code>true</code>
     * </ul></p>
     *
     * @param values the input array
     * @param begin index of the first array element to include
     * @param length the number of elements to include
     * @param allowEmpty if <code>true</code> then zero length arrays are allowed
     * @return true if the parameters are valid
     * @throws MathIllegalArgumentException if the indices are invalid or the array is null
     * @since 3.0
     */
    protected boolean test(final double[] values, final int begin,
            final int length, final boolean allowEmpty) throws MathIllegalArgumentException {
        return MathArrays.verifyValues(values, begin, length, allowEmpty);
    }

    /**
     * This method is used by <code>evaluate(double[], double[], int, int)</code> methods
     * to verify that the begin and length parameters designate a subarray of positive length
     * and the weights are all non-negative, non-NaN, finite, and not all zero.
     * <p>
     * <ul>
     * <li>returns <code>true</code> iff the parameters designate a subarray of
     * positive length and the weights array contains legitimate values.</li>
     * <li>throws <code>IllegalArgumentException</code> if any of the following are true:
     * <ul><li>the values array is null</li>
     *     <li>the weights array is null</li>
     *     <li>the weights array does not have the same length as the values array</li>
     *     <li>the weights array contains one or more infinite values</li>
     *     <li>the weights array contains one or more NaN values</li>
     *     <li>the weights array contains negative values</li>
     *     <li>the start and length arguments do not determine a valid array</li></ul>
     * </li>
     * <li>returns <code>false</li> if the array is non-null, but
     * <code>length</code> is 0.
     * </ul></p>
     *
     * @param values the input array
     * @param weights the weights array
     * @param begin index of the first array element to include
     * @param length the number of elements to include
     * @return true if the parameters are valid and designate a subarray of positive length
     * @throws MathIllegalArgumentException if the indices are invalid or the array is null
     * @since 2.1
     */
    protected boolean test(
        final double[] values,
        final double[] weights,
        final int begin,
        final int length) throws MathIllegalArgumentException {
        return MathArrays.verifyValues(values, weights, begin, length, false);
    }

    /**
     * This method is used by <code>evaluate(double[], double[], int, int)</code> methods
     * to verify that the begin and length parameters designate a subarray of positive length
     * and the weights are all non-negative, non-NaN, finite, and not all zero.
     * <p>
     * <ul>
     * <li>returns <code>true</code> iff the parameters designate a subarray of
     * non-negative length and the weights array contains legitimate values.</li>
     * <li>throws <code>MathIllegalArgumentException</code> if any of the following are true:
     * <ul><li>the values array is null</li>
     *     <li>the weights array is null</li>
     *     <li>the weights array does not have the same length as the values array</li>
     *     <li>the weights array contains one or more infinite values</li>
     *     <li>the weights array contains one or more NaN values</li>
     *     <li>the weights array contains negative values</li>
     *     <li>the start and length arguments do not determine a valid array</li></ul>
     * </li>
     * <li>returns <code>false</li> if the array is non-null, but
     * <code>length</code> is 0 unless <code>allowEmpty</code> is <code>true</code>.
     * </ul></p>
     *
     * @param values the input array.
     * @param weights the weights array.
     * @param begin index of the first array element to include.
     * @param length the number of elements to include.
     * @param allowEmpty if {@code true} than allow zero length arrays to pass.
     * @return {@code true} if the parameters are valid.
     * @throws NullArgumentException if either of the arrays are null
     * @throws MathIllegalArgumentException if the array indices are not valid,
     * the weights array contains NaN, infinite or negative elements, or there
     * are no positive weights.
     * @since 3.0
     */
    protected boolean test(final double[] values, final double[] weights,
            final int begin, final int length, final boolean allowEmpty) throws MathIllegalArgumentException {

        return MathArrays.verifyValues(values, weights, begin, length, allowEmpty);
    }
}

