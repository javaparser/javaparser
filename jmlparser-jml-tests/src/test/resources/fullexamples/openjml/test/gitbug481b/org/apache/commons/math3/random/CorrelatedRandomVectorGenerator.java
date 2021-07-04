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

package org.apache.commons.math3.random;

import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.linear.RealMatrix;
import org.apache.commons.math3.linear.RectangularCholeskyDecomposition;

/**
 * A {@link RandomVectorGenerator} that generates vectors with with
 * correlated components.
 * <p>Random vectors with correlated components are built by combining
 * the uncorrelated components of another random vector in such a way that
 * the resulting correlations are the ones specified by a positive
 * definite covariance matrix.</p>
 * <p>The main use for correlated random vector generation is for Monte-Carlo
 * simulation of physical problems with several variables, for example to
 * generate error vectors to be added to a nominal vector. A particularly
 * interesting case is when the generated vector should be drawn from a <a
 * href="http://en.wikipedia.org/wiki/Multivariate_normal_distribution">
 * Multivariate Normal Distribution</a>. The approach using a Cholesky
 * decomposition is quite usual in this case. However, it can be extended
 * to other cases as long as the underlying random generator provides
 * {@link NormalizedRandomGenerator normalized values} like {@link
 * GaussianRandomGenerator} or {@link UniformRandomGenerator}.</p>
 * <p>Sometimes, the covariance matrix for a given simulation is not
 * strictly positive definite. This means that the correlations are
 * not all independent from each other. In this case, however, the non
 * strictly positive elements found during the Cholesky decomposition
 * of the covariance matrix should not be negative either, they
 * should be null. Another non-conventional extension handling this case
 * is used here. Rather than computing <code>C = U<sup>T</sup>.U</code>
 * where <code>C</code> is the covariance matrix and <code>U</code>
 * is an upper-triangular matrix, we compute <code>C = B.B<sup>T</sup></code>
 * where <code>B</code> is a rectangular matrix having
 * more rows than columns. The number of columns of <code>B</code> is
 * the rank of the covariance matrix, and it is the dimension of the
 * uncorrelated random vector that is needed to compute the component
 * of the correlated vector. This class handles this situation
 * automatically.</p>
 *
 * @since 1.2
 */

public class CorrelatedRandomVectorGenerator
    implements RandomVectorGenerator {
    /** Mean vector. */
    private final double[] mean;
    /** Underlying generator. */
    private final NormalizedRandomGenerator generator;
    /** Storage for the normalized vector. */
    private final double[] normalized;
    /** Root of the covariance matrix. */
    private final RealMatrix root;

    /**
     * Builds a correlated random vector generator from its mean
     * vector and covariance matrix.
     *
     * @param mean Expected mean values for all components.
     * @param covariance Covariance matrix.
     * @param small Diagonal elements threshold under which  column are
     * considered to be dependent on previous ones and are discarded
     * @param generator underlying generator for uncorrelated normalized
     * components.
     * @throws org.apache.commons.math3.linear.NonPositiveDefiniteMatrixException
     * if the covariance matrix is not strictly positive definite.
     * @throws DimensionMismatchException if the mean and covariance
     * arrays dimensions do not match.
     */
    public CorrelatedRandomVectorGenerator(double[] mean,
                                           RealMatrix covariance, double small,
                                           NormalizedRandomGenerator generator) {
        int order = covariance.getRowDimension();
        if (mean.length != order) {
            throw new DimensionMismatchException(mean.length, order);
        }
        this.mean = mean.clone();

        final RectangularCholeskyDecomposition decomposition =
            new RectangularCholeskyDecomposition(covariance, small);
        root = decomposition.getRootMatrix();

        this.generator = generator;
        normalized = new double[decomposition.getRank()];

    }

    /**
     * Builds a null mean random correlated vector generator from its
     * covariance matrix.
     *
     * @param covariance Covariance matrix.
     * @param small Diagonal elements threshold under which  column are
     * considered to be dependent on previous ones and are discarded.
     * @param generator Underlying generator for uncorrelated normalized
     * components.
     * @throws org.apache.commons.math3.linear.NonPositiveDefiniteMatrixException
     * if the covariance matrix is not strictly positive definite.
     */
    public CorrelatedRandomVectorGenerator(RealMatrix covariance, double small,
                                           NormalizedRandomGenerator generator) {
        int order = covariance.getRowDimension();
        mean = new double[order];
        for (int i = 0; i < order; ++i) {
            mean[i] = 0;
        }

        final RectangularCholeskyDecomposition decomposition =
            new RectangularCholeskyDecomposition(covariance, small);
        root = decomposition.getRootMatrix();

        this.generator = generator;
        normalized = new double[decomposition.getRank()];

    }

    /** Get the underlying normalized components generator.
     * @return underlying uncorrelated components generator
     */
    public NormalizedRandomGenerator getGenerator() {
        return generator;
    }

    /** Get the rank of the covariance matrix.
     * The rank is the number of independent rows in the covariance
     * matrix, it is also the number of columns of the root matrix.
     * @return rank of the square matrix.
     * @see #getRootMatrix()
     */
    public int getRank() {
        return normalized.length;
    }

    /** Get the root of the covariance matrix.
     * The root is the rectangular matrix <code>B</code> such that
     * the covariance matrix is equal to <code>B.B<sup>T</sup></code>
     * @return root of the square matrix
     * @see #getRank()
     */
    public RealMatrix getRootMatrix() {
        return root;
    }

    /** Generate a correlated random vector.
     * @return a random vector as an array of double. The returned array
     * is created at each call, the caller can do what it wants with it.
     */
    public double[] nextVector() {

        // generate uncorrelated vector
        for (int i = 0; i < normalized.length; ++i) {
            normalized[i] = generator.nextNormalizedDouble();
        }

        // compute correlated vector
        double[] correlated = new double[mean.length];
        for (int i = 0; i < correlated.length; ++i) {
            correlated[i] = mean[i];
            for (int j = 0; j < root.getColumnDimension(); ++j) {
                correlated[i] += root.getEntry(i, j) * normalized[j];
            }
        }

        return correlated;

    }

}
