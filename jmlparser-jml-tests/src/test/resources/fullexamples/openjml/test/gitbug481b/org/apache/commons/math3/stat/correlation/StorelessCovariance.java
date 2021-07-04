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

import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.MathUnsupportedOperationException;
import org.apache.commons.math3.exception.NumberIsTooSmallException;
import org.apache.commons.math3.linear.MatrixUtils;
import org.apache.commons.math3.linear.RealMatrix;

/**
 * Covariance implementation that does not require input data to be
 * stored in memory. The size of the covariance matrix is specified in the
 * constructor. Specific elements of the matrix are incrementally updated with
 * calls to incrementRow() or increment Covariance().
 *
 * <p>This class is based on a paper written by Philippe P&eacute;bay:
 * <a href="http://prod.sandia.gov/techlib/access-control.cgi/2008/086212.pdf">
 * Formulas for Robust, One-Pass Parallel Computation of Covariances and
 * Arbitrary-Order Statistical Moments</a>, 2008, Technical Report SAND2008-6212,
 * Sandia National Laboratories.</p>
 *
 * <p>Note: the underlying covariance matrix is symmetric, thus only the
 * upper triangular part of the matrix is stored and updated each increment.</p>
 *
 * @since 3.0
 */
public class StorelessCovariance extends Covariance {

    /** the square covariance matrix (upper triangular part) */
    private StorelessBivariateCovariance[] covMatrix;

    /** dimension of the square covariance matrix */
    private int dimension;

    /**
     * Create a bias corrected covariance matrix with a given dimension.
     *
     * @param dim the dimension of the square covariance matrix
     */
    public StorelessCovariance(final int dim) {
        this(dim, true);
    }

    /**
     * Create a covariance matrix with a given number of rows and columns and the
     * indicated bias correction.
     *
     * @param dim the dimension of the covariance matrix
     * @param biasCorrected if <code>true</code> the covariance estimate is corrected
     * for bias, i.e. n-1 in the denominator, otherwise there is no bias correction,
     * i.e. n in the denominator.
     */
    public StorelessCovariance(final int dim, final boolean biasCorrected) {
        dimension = dim;
        covMatrix = new StorelessBivariateCovariance[dimension * (dimension + 1) / 2];
        initializeMatrix(biasCorrected);
    }

    /**
     * Initialize the internal two-dimensional array of
     * {@link StorelessBivariateCovariance} instances.
     *
     * @param biasCorrected if the covariance estimate shall be corrected for bias
     */
    private void initializeMatrix(final boolean biasCorrected) {
        for(int i = 0; i < dimension; i++){
            for(int j = 0; j < dimension; j++){
                setElement(i, j, new StorelessBivariateCovariance(biasCorrected));
            }
        }
    }

    /**
     * Returns the index (i, j) translated into the one-dimensional
     * array used to store the upper triangular part of the symmetric
     * covariance matrix.
     *
     * @param i the row index
     * @param j the column index
     * @return the corresponding index in the matrix array
     */
    private int indexOf(final int i, final int j) {
        return j < i ? i * (i + 1) / 2 + j : j * (j + 1) / 2 + i;
    }

    /**
     * Gets the element at index (i, j) from the covariance matrix
     * @param i the row index
     * @param j the column index
     * @return the {@link StorelessBivariateCovariance} element at the given index
     */
    private StorelessBivariateCovariance getElement(final int i, final int j) {
        return covMatrix[indexOf(i, j)];
    }

    /**
     * Sets the covariance element at index (i, j) in the covariance matrix
     * @param i the row index
     * @param j the column index
     * @param cov the {@link StorelessBivariateCovariance} element to be set
     */
    private void setElement(final int i, final int j,
                            final StorelessBivariateCovariance cov) {
        covMatrix[indexOf(i, j)] = cov;
    }

    /**
     * Get the covariance for an individual element of the covariance matrix.
     *
     * @param xIndex row index in the covariance matrix
     * @param yIndex column index in the covariance matrix
     * @return the covariance of the given element
     * @throws NumberIsTooSmallException if the number of observations
     * in the cell is &lt; 2
     */
    public double getCovariance(final int xIndex,
                                final int yIndex)
        throws NumberIsTooSmallException {

        return getElement(xIndex, yIndex).getResult();

    }

    /**
     * Increment the covariance matrix with one row of data.
     *
     * @param data array representing one row of data.
     * @throws DimensionMismatchException if the length of <code>rowData</code>
     * does not match with the covariance matrix
     */
    public void increment(final double[] data)
        throws DimensionMismatchException {

        int length = data.length;
        if (length != dimension) {
            throw new DimensionMismatchException(length, dimension);
        }

        // only update the upper triangular part of the covariance matrix
        // as only these parts are actually stored
        for (int i = 0; i < length; i++){
            for (int j = i; j < length; j++){
                getElement(i, j).increment(data[i], data[j]);
            }
        }

    }

    /**
     * Appends {@code sc} to this, effectively aggregating the computations in {@code sc}
     * with this.  After invoking this method, covariances returned should be close
     * to what would have been obtained by performing all of the {@link #increment(double[])}
     * operations in {@code sc} directly on this.
     *
     * @param sc externally computed StorelessCovariance to add to this
     * @throws DimensionMismatchException if the dimension of sc does not match this
     * @since 3.3
     */
    public void append(StorelessCovariance sc) throws DimensionMismatchException {
        if (sc.dimension != dimension) {
            throw new DimensionMismatchException(sc.dimension, dimension);
        }

        // only update the upper triangular part of the covariance matrix
        // as only these parts are actually stored
        for (int i = 0; i < dimension; i++) {
            for (int j = i; j < dimension; j++) {
                getElement(i, j).append(sc.getElement(i, j));
            }
        }
    }

    /**
     * {@inheritDoc}
     * @throws NumberIsTooSmallException if the number of observations
     * in a cell is &lt; 2
     */
    @Override
    public RealMatrix getCovarianceMatrix() throws NumberIsTooSmallException {
        return MatrixUtils.createRealMatrix(getData());
    }

    /**
     * Return the covariance matrix as two-dimensional array.
     *
     * @return a two-dimensional double array of covariance values
     * @throws NumberIsTooSmallException if the number of observations
     * for a cell is &lt; 2
     */
    public double[][] getData() throws NumberIsTooSmallException {
        final double[][] data = new double[dimension][dimension];
        for (int i = 0; i < dimension; i++) {
            for (int j = 0; j < dimension; j++) {
                data[i][j] = getElement(i, j).getResult();
            }
        }
        return data;
    }

    /**
     * This {@link Covariance} method is not supported by a {@link StorelessCovariance},
     * since the number of bivariate observations does not have to be the same for different
     * pairs of covariates - i.e., N as defined in {@link Covariance#getN()} is undefined.
     *
     * @return nothing as this implementation always throws a
     * {@link MathUnsupportedOperationException}
     * @throws MathUnsupportedOperationException in all cases
     */
    @Override
    public int getN()
        throws MathUnsupportedOperationException {
        throw new MathUnsupportedOperationException();
    }
}
