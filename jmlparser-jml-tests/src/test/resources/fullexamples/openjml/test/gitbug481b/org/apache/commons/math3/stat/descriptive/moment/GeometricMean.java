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
package org.apache.commons.math3.stat.descriptive.moment;

import java.io.Serializable;

import org.apache.commons.math3.exception.MathIllegalArgumentException;
import org.apache.commons.math3.exception.MathIllegalStateException;
import org.apache.commons.math3.exception.NullArgumentException;
import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.stat.descriptive.AbstractStorelessUnivariateStatistic;
import org.apache.commons.math3.stat.descriptive.StorelessUnivariateStatistic;
import org.apache.commons.math3.stat.descriptive.summary.SumOfLogs;
import org.apache.commons.math3.util.FastMath;
import org.apache.commons.math3.util.MathUtils;

/**
 * Returns the <a href="http://www.xycoon.com/geometric_mean.htm">
 * geometric mean </a> of the available values.
 * <p>
 * Uses a {@link SumOfLogs} instance to compute sum of logs and returns
 * <code> exp( 1/n  (sum of logs) ).</code>  Therefore, </p>
 * <ul>
 * <li>If any of values are < 0, the result is <code>NaN.</code></li>
 * <li>If all values are non-negative and less than
 * <code>Double.POSITIVE_INFINITY</code>,  but at least one value is 0, the
 * result is <code>0.</code></li>
 * <li>If both <code>Double.POSITIVE_INFINITY</code> and
 * <code>Double.NEGATIVE_INFINITY</code> are among the values, the result is
 * <code>NaN.</code></li>
 * </ul> </p>
 * <p>
 * <strong>Note that this implementation is not synchronized.</strong> If
 * multiple threads access an instance of this class concurrently, and at least
 * one of the threads invokes the <code>increment()</code> or
 * <code>clear()</code> method, it must be synchronized externally.</p>
 *
 *
 */
public class GeometricMean extends AbstractStorelessUnivariateStatistic implements Serializable {

    /** Serializable version identifier */
    private static final long serialVersionUID = -8178734905303459453L;

    /** Wrapped SumOfLogs instance */
    private StorelessUnivariateStatistic sumOfLogs;

    /**
     * Create a GeometricMean instance
     */
    public GeometricMean() {
        sumOfLogs = new SumOfLogs();
    }

    /**
     * Copy constructor, creates a new {@code GeometricMean} identical
     * to the {@code original}
     *
     * @param original the {@code GeometricMean} instance to copy
     * @throws NullArgumentException if original is null
     */
    public GeometricMean(GeometricMean original) throws NullArgumentException {
        super();
        copy(original, this);
    }

    /**
     * Create a GeometricMean instance using the given SumOfLogs instance
     * @param sumOfLogs sum of logs instance to use for computation
     */
    public GeometricMean(SumOfLogs sumOfLogs) {
        this.sumOfLogs = sumOfLogs;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public GeometricMean copy() {
        GeometricMean result = new GeometricMean();
        // no try-catch or advertised exception because args guaranteed non-null
        copy(this, result);
        return result;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void increment(final double d) {
        sumOfLogs.increment(d);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public double getResult() {
        if (sumOfLogs.getN() > 0) {
            return FastMath.exp(sumOfLogs.getResult() / sumOfLogs.getN());
        } else {
            return Double.NaN;
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void clear() {
        sumOfLogs.clear();
    }

    /**
     * Returns the geometric mean of the entries in the specified portion
     * of the input array.
     * <p>
     * See {@link GeometricMean} for details on the computing algorithm.</p>
     * <p>
     * Throws <code>IllegalArgumentException</code> if the array is null.</p>
     *
     * @param values input array containing the values
     * @param begin first array element to include
     * @param length the number of elements to include
     * @return the geometric mean or Double.NaN if length = 0 or
     * any of the values are &lt;= 0.
     * @throws MathIllegalArgumentException if the input array is null or the array
     * index parameters are not valid
     */
    @Override
    public double evaluate(
        final double[] values, final int begin, final int length)
    throws MathIllegalArgumentException {
        return FastMath.exp(
            sumOfLogs.evaluate(values, begin, length) / length);
    }

    /**
     * {@inheritDoc}
     */
    public long getN() {
        return sumOfLogs.getN();
    }

    /**
     * <p>Sets the implementation for the sum of logs.</p>
     * <p>This method must be activated before any data has been added - i.e.,
     * before {@link #increment(double) increment} has been used to add data;
     * otherwise an IllegalStateException will be thrown.</p>
     *
     * @param sumLogImpl the StorelessUnivariateStatistic instance to use
     * for computing the log sum
     * @throws MathIllegalStateException if data has already been added
     *  (i.e if n > 0)
     */
    public void setSumLogImpl(StorelessUnivariateStatistic sumLogImpl)
    throws MathIllegalStateException {
        checkEmpty();
        this.sumOfLogs = sumLogImpl;
    }

    /**
     * Returns the currently configured sum of logs implementation
     *
     * @return the StorelessUnivariateStatistic implementing the log sum
     */
    public StorelessUnivariateStatistic getSumLogImpl() {
        return sumOfLogs;
    }

    /**
     * Copies source to dest.
     * <p>Neither source nor dest can be null.</p>
     *
     * @param source GeometricMean to copy
     * @param dest GeometricMean to copy to
     * @throws NullArgumentException if either source or dest is null
     */
    public static void copy(GeometricMean source, GeometricMean dest)
        throws NullArgumentException {
        MathUtils.checkNotNull(source);
        MathUtils.checkNotNull(dest);
        dest.setData(source.getDataRef());
        dest.sumOfLogs = source.sumOfLogs.copy();
    }


    /**
     * Throws MathIllegalStateException if n > 0.
     * @throws MathIllegalStateException if data has been added to this statistic
     */
    private void checkEmpty() throws MathIllegalStateException {
        if (getN() > 0) {
            throw new MathIllegalStateException(
                    LocalizedFormats.VALUES_ADDED_BEFORE_CONFIGURING_STATISTIC,
                    getN());
        }
    }

}
