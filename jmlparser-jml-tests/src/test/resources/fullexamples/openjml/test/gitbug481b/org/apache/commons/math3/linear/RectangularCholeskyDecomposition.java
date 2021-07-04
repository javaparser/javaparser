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

package org.apache.commons.math3.linear;

import org.apache.commons.math3.util.FastMath;

/**
 * Calculates the rectangular Cholesky decomposition of a matrix.
 * <p>The rectangular Cholesky decomposition of a real symmetric positive
 * semidefinite matrix A consists of a rectangular matrix B with the same
 * number of rows such that: A is almost equal to BB<sup>T</sup>, depending
 * on a user-defined tolerance. In a sense, this is the square root of A.</p>
 * <p>The difference with respect to the regular {@link CholeskyDecomposition}
 * is that rows/columns may be permuted (hence the rectangular shape instead
 * of the traditional triangular shape) and there is a threshold to ignore
 * small diagonal elements. This is used for example to generate {@link
 * org.apache.commons.math3.random.CorrelatedRandomVectorGenerator correlated
 * random n-dimensions vectors} in a p-dimension subspace (p < n).
 * In other words, it allows generating random vectors from a covariance
 * matrix that is only positive semidefinite, and not positive definite.</p>
 * <p>Rectangular Cholesky decomposition is <em>not</em> suited for solving
 * linear systems, so it does not provide any {@link DecompositionSolver
 * decomposition solver}.</p>
 *
 * @see <a href="http://mathworld.wolfram.com/CholeskyDecomposition.html">MathWorld</a>
 * @see <a href="http://en.wikipedia.org/wiki/Cholesky_decomposition">Wikipedia</a>
 * @since 2.0 (changed to concrete class in 3.0)
 */
public class RectangularCholeskyDecomposition {

    /** Permutated Cholesky root of the symmetric positive semidefinite matrix. */
    private final RealMatrix root;

    /** Rank of the symmetric positive semidefinite matrix. */
    private int rank;

    /**
     * Decompose a symmetric positive semidefinite matrix.
     * <p>
     * <b>Note:</b> this constructor follows the linpack method to detect dependent
     * columns by proceeding with the Cholesky algorithm until a nonpositive diagonal
     * element is encountered.
     *
     * @see <a href="http://eprints.ma.man.ac.uk/1193/01/covered/MIMS_ep2008_56.pdf">
     * Analysis of the Cholesky Decomposition of a Semi-definite Matrix</a>
     *
     * @param matrix Symmetric positive semidefinite matrix.
     * @exception NonPositiveDefiniteMatrixException if the matrix is not
     * positive semidefinite.
     * @since 3.1
     */
    public RectangularCholeskyDecomposition(RealMatrix matrix)
        throws NonPositiveDefiniteMatrixException {
        this(matrix, 0);
    }

    /**
     * Decompose a symmetric positive semidefinite matrix.
     *
     * @param matrix Symmetric positive semidefinite matrix.
     * @param small Diagonal elements threshold under which columns are
     * considered to be dependent on previous ones and are discarded.
     * @exception NonPositiveDefiniteMatrixException if the matrix is not
     * positive semidefinite.
     */
    public RectangularCholeskyDecomposition(RealMatrix matrix, double small)
        throws NonPositiveDefiniteMatrixException {

        final int order = matrix.getRowDimension();
        final double[][] c = matrix.getData();
        final double[][] b = new double[order][order];

        int[] index = new int[order];
        for (int i = 0; i < order; ++i) {
            index[i] = i;
        }

        int r = 0;
        for (boolean loop = true; loop;) {

            // find maximal diagonal element
            int swapR = r;
            for (int i = r + 1; i < order; ++i) {
                int ii  = index[i];
                int isr = index[swapR];
                if (c[ii][ii] > c[isr][isr]) {
                    swapR = i;
                }
            }


            // swap elements
            if (swapR != r) {
                final int tmpIndex    = index[r];
                index[r]              = index[swapR];
                index[swapR]          = tmpIndex;
                final double[] tmpRow = b[r];
                b[r]                  = b[swapR];
                b[swapR]              = tmpRow;
            }

            // check diagonal element
            int ir = index[r];
            if (c[ir][ir] <= small) {

                if (r == 0) {
                    throw new NonPositiveDefiniteMatrixException(c[ir][ir], ir, small);
                }

                // check remaining diagonal elements
                for (int i = r; i < order; ++i) {
                    if (c[index[i]][index[i]] < -small) {
                        // there is at least one sufficiently negative diagonal element,
                        // the symmetric positive semidefinite matrix is wrong
                        throw new NonPositiveDefiniteMatrixException(c[index[i]][index[i]], i, small);
                    }
                }

                // all remaining diagonal elements are close to zero, we consider we have
                // found the rank of the symmetric positive semidefinite matrix
                loop = false;

            } else {

                // transform the matrix
                final double sqrt = FastMath.sqrt(c[ir][ir]);
                b[r][r] = sqrt;
                final double inverse  = 1 / sqrt;
                final double inverse2 = 1 / c[ir][ir];
                for (int i = r + 1; i < order; ++i) {
                    final int ii = index[i];
                    final double e = inverse * c[ii][ir];
                    b[i][r] = e;
                    c[ii][ii] -= c[ii][ir] * c[ii][ir] * inverse2;
                    for (int j = r + 1; j < i; ++j) {
                        final int ij = index[j];
                        final double f = c[ii][ij] - e * b[j][r];
                        c[ii][ij] = f;
                        c[ij][ii] = f;
                    }
                }

                // prepare next iteration
                loop = ++r < order;
            }
        }

        // build the root matrix
        rank = r;
        root = MatrixUtils.createRealMatrix(order, r);
        for (int i = 0; i < order; ++i) {
            for (int j = 0; j < r; ++j) {
                root.setEntry(index[i], j, b[i][j]);
            }
        }

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

    /** Get the rank of the symmetric positive semidefinite matrix.
     * The r is the number of independent rows in the symmetric positive semidefinite
     * matrix, it is also the number of columns of the rectangular
     * matrix of the decomposition.
     * @return r of the square matrix.
     * @see #getRootMatrix()
     */
    public int getRank() {
        return rank;
    }

}
