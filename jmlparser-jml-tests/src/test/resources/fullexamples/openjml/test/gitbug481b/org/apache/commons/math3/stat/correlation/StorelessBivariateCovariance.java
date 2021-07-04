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
package org.apache.commons.math3.stat.correlation;

import org.apache.commons.math3.exception.NumberIsTooSmallException;
import org.apache.commons.math3.exception.util.LocalizedFormats;

/**
 * Bivariate Covariance implementation that does not require input data to be
 * stored in memory.
 *
 * <p>This class is based on a paper written by Philippe P&eacute;bay:
 * <a href="http://prod.sandia.gov/techlib/access-control.cgi/2008/086212.pdf">
 * Formulas for Robust, One-Pass Parallel Computation of Covariances and
 * Arbitrary-Order Statistical Moments</a>, 2008, Technical Report SAND2008-6212,
 * Sandia National Laboratories. It computes the covariance for a pair of variables.
 * Use {@link StorelessCovariance} to estimate an entire covariance matrix.</p>
 *
 * <p>Note: This class is package private as it is only used internally in
 * the {@link StorelessCovariance} class.</p>
 *
 * @since 3.0
 */
class StorelessBivariateCovariance {

    /** the mean of variable x */
    private double meanX;

    /** the mean of variable y */
    private double meanY;

    /** number of observations */
    private double n;

    /** the running covariance estimate */
    private double covarianceNumerator;

    /** flag for bias correction */
    private boolean biasCorrected;

    /**
     * Create an empty {@link StorelessBivariateCovariance} instance with
     * bias correction.
     */
    StorelessBivariateCovariance() {
        this(true);
    }

    /**
     * Create an empty {@link StorelessBivariateCovariance} instance.
     *
     * @param biasCorrection if <code>true</code> the covariance estimate is corrected
     * for bias, i.e. n-1 in the denominator, otherwise there is no bias correction,
     * i.e. n in the denominator.
     */
    StorelessBivariateCovariance(final boolean biasCorrection) {
        meanX = meanY = 0.0;
        n = 0;
        covarianceNumerator = 0.0;
        biasCorrected = biasCorrection;
    }

    /**
     * Update the covariance estimation with a pair of variables (x, y).
     *
     * @param x the x value
     * @param y the y value
     */
    public void increment(final double x, final double y) {
        n++;
        final double deltaX = x - meanX;
        final double deltaY = y - meanY;
        meanX += deltaX / n;
        meanY += deltaY / n;
        covarianceNumerator += ((n - 1.0) / n) * deltaX * deltaY;
    }

    /**
     * Appends another bivariate covariance calculation to this.
     * After this operation, statistics returned should be close to what would
     * have been obtained by by performing all of the {@link #increment(double, double)}
     * operations in {@code cov} directly on this.
     *
     * @param cov StorelessBivariateCovariance instance to append.
     */
    public void append(StorelessBivariateCovariance cov) {
        double oldN = n;
        n += cov.n;
        final double deltaX = cov.meanX - meanX;
        final double deltaY = cov.meanY - meanY;
        meanX += deltaX * cov.n / n;
        meanY += deltaY * cov.n / n;
        covarianceNumerator += cov.covarianceNumerator + oldN * cov.n / n * deltaX * deltaY;
    }

    /**
     * Returns the number of observations.
     *
     * @return number of observations
     */
    public double getN() {
        return n;
    }

    /**
     * Return the current covariance estimate.
     *
     * @return the current covariance
     * @throws NumberIsTooSmallException if the number of observations
     * is &lt; 2
     */
    public double getResult() throws NumberIsTooSmallException {
        if (n < 2) {
            throw new NumberIsTooSmallException(LocalizedFormats.INSUFFICIENT_DIMENSION,
                                                n, 2, true);
        }
        if (biasCorrected) {
            return covarianceNumerator / (n - 1d);
        } else {
            return covarianceNumerator / n;
        }
    }
}

