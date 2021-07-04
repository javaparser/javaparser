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

import org.apache.commons.math3.exception.MathIllegalArgumentException;
import org.apache.commons.math3.exception.NullArgumentException;
import org.apache.commons.math3.util.MathUtils;

/**
 * Implementation of
 * {@link org.apache.commons.math3.stat.descriptive.DescriptiveStatistics} that
 * is safe to use in a multithreaded environment.  Multiple threads can safely
 * operate on a single instance without causing runtime exceptions due to race
 * conditions.  In effect, this implementation makes modification and access
 * methods atomic operations for a single instance.  That is to say, as one
 * thread is computing a statistic from the instance, no other thread can modify
 * the instance nor compute another statistic.
 *
 * @since 1.2
 */
public class SynchronizedDescriptiveStatistics extends DescriptiveStatistics {

    /** Serialization UID */
    private static final long serialVersionUID = 1L;

    /**
     * Construct an instance with infinite window
     */
    public SynchronizedDescriptiveStatistics() {
        // no try-catch or advertized IAE because arg is valid
        this(INFINITE_WINDOW);
    }

    /**
     * Construct an instance with finite window
     * @param window the finite window size.
     * @throws MathIllegalArgumentException if window size is less than 1 but
     * not equal to {@link #INFINITE_WINDOW}
     */
    public SynchronizedDescriptiveStatistics(int window) throws MathIllegalArgumentException {
        super(window);
    }

    /**
     * A copy constructor. Creates a deep-copy of the {@code original}.
     *
     * @param original the {@code SynchronizedDescriptiveStatistics} instance to copy
     * @throws NullArgumentException if original is null
     */
    public SynchronizedDescriptiveStatistics(SynchronizedDescriptiveStatistics original)
    throws NullArgumentException {
        copy(original, this);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public synchronized void addValue(double v) {
        super.addValue(v);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public synchronized double apply(UnivariateStatistic stat) {
        return super.apply(stat);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public synchronized void clear() {
        super.clear();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public synchronized double getElement(int index) {
        return super.getElement(index);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public synchronized long getN() {
        return super.getN();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public synchronized double getStandardDeviation() {
        return super.getStandardDeviation();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public synchronized double getQuadraticMean() {
        return super.getQuadraticMean();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public synchronized double[] getValues() {
        return super.getValues();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public synchronized int getWindowSize() {
        return super.getWindowSize();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public synchronized void setWindowSize(int windowSize) throws MathIllegalArgumentException {
        super.setWindowSize(windowSize);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public synchronized String toString() {
        return super.toString();
    }

    /**
     * Returns a copy of this SynchronizedDescriptiveStatistics instance with the
     * same internal state.
     *
     * @return a copy of this
     */
    @Override
    public synchronized SynchronizedDescriptiveStatistics copy() {
        SynchronizedDescriptiveStatistics result =
            new SynchronizedDescriptiveStatistics();
        // No try-catch or advertised exception because arguments are guaranteed non-null
        copy(this, result);
        return result;
    }

    /**
     * Copies source to dest.
     * <p>Neither source nor dest can be null.</p>
     * <p>Acquires synchronization lock on source, then dest before copying.</p>
     *
     * @param source SynchronizedDescriptiveStatistics to copy
     * @param dest SynchronizedDescriptiveStatistics to copy to
     * @throws NullArgumentException if either source or dest is null
     */
    public static void copy(SynchronizedDescriptiveStatistics source,
                            SynchronizedDescriptiveStatistics dest)
        throws NullArgumentException {
        MathUtils.checkNotNull(source);
        MathUtils.checkNotNull(dest);
        synchronized (source) {
            synchronized (dest) {
                DescriptiveStatistics.copy(source, dest);
            }
        }
    }
}
