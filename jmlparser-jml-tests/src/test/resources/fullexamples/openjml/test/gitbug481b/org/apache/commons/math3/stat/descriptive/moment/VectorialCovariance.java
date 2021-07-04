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
import java.util.Arrays;

import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.linear.MatrixUtils;
import org.apache.commons.math3.linear.RealMatrix;

/**
 * Returns the covariance matrix of the available vectors.
 * @since 1.2
 */
public class VectorialCovariance implements Serializable {

    /** Serializable version identifier */
    private static final long serialVersionUID = 4118372414238930270L;

    /** Sums for each component. */
    private final double[] sums;

    /** Sums of products for each component. */
    private final double[] productsSums;

    /** Indicator for bias correction. */
    private final boolean isBiasCorrected;

    /** Number of vectors in the sample. */
    private long n;

    /** Constructs a VectorialCovariance.
     * @param dimension vectors dimension
     * @param isBiasCorrected if true, computed the unbiased sample covariance,
     * otherwise computes the biased population covariance
     */
    public VectorialCovariance(int dimension, boolean isBiasCorrected) {
        sums         = new double[dimension];
        productsSums = new double[dimension * (dimension + 1) / 2];
        n            = 0;
        this.isBiasCorrected = isBiasCorrected;
    }

    /**
     * Add a new vector to the sample.
     * @param v vector to add
     * @throws DimensionMismatchException if the vector does not have the right dimension
     */
    public void increment(double[] v) throws DimensionMismatchException {
        if (v.length != sums.length) {
            throw new DimensionMismatchException(v.length, sums.length);
        }
        int k = 0;
        for (int i = 0; i < v.length; ++i) {
            sums[i] += v[i];
            for (int j = 0; j <= i; ++j) {
                productsSums[k++] += v[i] * v[j];
            }
        }
        n++;
    }

    /**
     * Get the covariance matrix.
     * @return covariance matrix
     */
    public RealMatrix getResult() {

        int dimension = sums.length;
        RealMatrix result = MatrixUtils.createRealMatrix(dimension, dimension);

        if (n > 1) {
            double c = 1.0 / (n * (isBiasCorrected ? (n - 1) : n));
            int k = 0;
            for (int i = 0; i < dimension; ++i) {
                for (int j = 0; j <= i; ++j) {
                    double e = c * (n * productsSums[k++] - sums[i] * sums[j]);
                    result.setEntry(i, j, e);
                    result.setEntry(j, i, e);
                }
            }
        }

        return result;

    }

    /**
     * Get the number of vectors in the sample.
     * @return number of vectors in the sample
     */
    public long getN() {
        return n;
    }

    /**
     * Clears the internal state of the Statistic
     */
    public void clear() {
        n = 0;
        Arrays.fill(sums, 0.0);
        Arrays.fill(productsSums, 0.0);
    }

    /** {@inheritDoc} */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + (isBiasCorrected ? 1231 : 1237);
        result = prime * result + (int) (n ^ (n >>> 32));
        result = prime * result + Arrays.hashCode(productsSums);
        result = prime * result + Arrays.hashCode(sums);
        return result;
    }

    /** {@inheritDoc} */
    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (!(obj instanceof VectorialCovariance)) {
            return false;
        }
        VectorialCovariance other = (VectorialCovariance) obj;
        if (isBiasCorrected != other.isBiasCorrected) {
            return false;
        }
        if (n != other.n) {
            return false;
        }
        if (!Arrays.equals(productsSums, other.productsSums)) {
            return false;
        }
        if (!Arrays.equals(sums, other.sums)) {
            return false;
        }
        return true;
    }

}
