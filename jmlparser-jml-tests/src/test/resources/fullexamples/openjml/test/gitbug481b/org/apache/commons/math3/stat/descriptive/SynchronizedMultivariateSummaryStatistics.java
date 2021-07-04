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

import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.MathIllegalStateException;
import org.apache.commons.math3.linear.RealMatrix;

/**
 * Implementation of
 * {@link org.apache.commons.math3.stat.descriptive.MultivariateSummaryStatistics} that
 * is safe to use in a multithreaded environment.  Multiple threads can safely
 * operate on a single instance without causing runtime exceptions due to race
 * conditions.  In effect, this implementation makes modification and access
 * methods atomic operations for a single instance.  That is to say, as one
 * thread is computing a statistic from the instance, no other thread can modify
 * the instance nor compute another statistic.
 * @since 1.2
 */
public class SynchronizedMultivariateSummaryStatistics
    extends MultivariateSummaryStatistics {

    /** Serialization UID */
    private static final long serialVersionUID = 7099834153347155363L;

    /**
     * Construct a SynchronizedMultivariateSummaryStatistics instance
     * @param k dimension of the data
     * @param isCovarianceBiasCorrected if true, the unbiased sample
     * covariance is computed, otherwise the biased population covariance
     * is computed
     */
    public SynchronizedMultivariateSummaryStatistics(int k, boolean isCovarianceBiasCorrected) {
        super(k, isCovarianceBiasCorrected);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public synchronized void addValue(double[] value) throws DimensionMismatchException {
      super.addValue(value);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public synchronized int getDimension() {
        return super.getDimension();
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
    public synchronized double[] getSum() {
        return super.getSum();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public synchronized double[] getSumSq() {
        return super.getSumSq();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public synchronized double[] getSumLog() {
        return super.getSumLog();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public synchronized double[] getMean() {
        return super.getMean();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public synchronized double[] getStandardDeviation() {
        return super.getStandardDeviation();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public synchronized RealMatrix getCovariance() {
        return super.getCovariance();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public synchronized double[] getMax() {
        return super.getMax();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public synchronized double[] getMin() {
        return super.getMin();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public synchronized double[] getGeometricMean() {
        return super.getGeometricMean();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public synchronized String toString() {
        return super.toString();
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
    public synchronized boolean equals(Object object) {
        return super.equals(object);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public synchronized int hashCode() {
        return super.hashCode();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public synchronized StorelessUnivariateStatistic[] getSumImpl() {
        return super.getSumImpl();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public synchronized void setSumImpl(StorelessUnivariateStatistic[] sumImpl)
    throws DimensionMismatchException, MathIllegalStateException {
        super.setSumImpl(sumImpl);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public synchronized StorelessUnivariateStatistic[] getSumsqImpl() {
        return super.getSumsqImpl();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public synchronized void setSumsqImpl(StorelessUnivariateStatistic[] sumsqImpl)
    throws DimensionMismatchException, MathIllegalStateException {
        super.setSumsqImpl(sumsqImpl);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public synchronized StorelessUnivariateStatistic[] getMinImpl() {
        return super.getMinImpl();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public synchronized void setMinImpl(StorelessUnivariateStatistic[] minImpl)
    throws DimensionMismatchException, MathIllegalStateException {
        super.setMinImpl(minImpl);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public synchronized StorelessUnivariateStatistic[] getMaxImpl() {
        return super.getMaxImpl();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public synchronized void setMaxImpl(StorelessUnivariateStatistic[] maxImpl)
    throws DimensionMismatchException, MathIllegalStateException{
        super.setMaxImpl(maxImpl);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public synchronized StorelessUnivariateStatistic[] getSumLogImpl() {
        return super.getSumLogImpl();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public synchronized void setSumLogImpl(StorelessUnivariateStatistic[] sumLogImpl)
    throws DimensionMismatchException, MathIllegalStateException {
        super.setSumLogImpl(sumLogImpl);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public synchronized StorelessUnivariateStatistic[] getGeoMeanImpl() {
        return super.getGeoMeanImpl();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public synchronized void setGeoMeanImpl(StorelessUnivariateStatistic[] geoMeanImpl)
    throws DimensionMismatchException, MathIllegalStateException {
        super.setGeoMeanImpl(geoMeanImpl);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public synchronized StorelessUnivariateStatistic[] getMeanImpl() {
        return super.getMeanImpl();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public synchronized void setMeanImpl(StorelessUnivariateStatistic[] meanImpl)
    throws DimensionMismatchException, MathIllegalStateException {
        super.setMeanImpl(meanImpl);
    }
}
