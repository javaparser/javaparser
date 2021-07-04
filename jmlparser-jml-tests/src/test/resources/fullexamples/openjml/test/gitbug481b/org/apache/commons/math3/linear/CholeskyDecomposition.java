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

import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.util.FastMath;


/**
 * Calculates the Cholesky decomposition of a matrix.
 * <p>The Cholesky decomposition of a real symmetric positive-definite
 * matrix A consists of a lower triangular matrix L with same size such
 * that: A = LL<sup>T</sup>. In a sense, this is the square root of A.</p>
 * <p>This class is based on the class with similar name from the
 * <a href="http://math.nist.gov/javanumerics/jama/">JAMA</a> library, with the
 * following changes:</p>
 * <ul>
 *   <li>a {@link #getLT() getLT} method has been added,</li>
 *   <li>the {@code isspd} method has been removed, since the constructor of
 *   this class throws a {@link NonPositiveDefiniteMatrixException} when a
 *   matrix cannot be decomposed,</li>
 *   <li>a {@link #getDeterminant() getDeterminant} method has been added,</li>
 *   <li>the {@code solve} method has been replaced by a {@link #getSolver()
 *   getSolver} method and the equivalent method provided by the returned
 *   {@link DecompositionSolver}.</li>
 * </ul>
 *
 * @see <a href="http://mathworld.wolfram.com/CholeskyDecomposition.html">MathWorld</a>
 * @see <a href="http://en.wikipedia.org/wiki/Cholesky_decomposition">Wikipedia</a>
 * @since 2.0 (changed to concrete class in 3.0)
 */
public class CholeskyDecomposition {
    /**
     * Default threshold above which off-diagonal elements are considered too different
     * and matrix not symmetric.
     */
    public static final double DEFAULT_RELATIVE_SYMMETRY_THRESHOLD = 1.0e-15;
    /**
     * Default threshold below which diagonal elements are considered null
     * and matrix not positive definite.
     */
    public static final double DEFAULT_ABSOLUTE_POSITIVITY_THRESHOLD = 1.0e-10;
    /** Row-oriented storage for L<sup>T</sup> matrix data. */
    private double[][] lTData;
    /** Cached value of L. */
    private RealMatrix cachedL;
    /** Cached value of LT. */
    private RealMatrix cachedLT;

    /**
     * Calculates the Cholesky decomposition of the given matrix.
     * <p>
     * Calling this constructor is equivalent to call {@link
     * #CholeskyDecomposition(RealMatrix, double, double)} with the
     * thresholds set to the default values {@link
     * #DEFAULT_RELATIVE_SYMMETRY_THRESHOLD} and {@link
     * #DEFAULT_ABSOLUTE_POSITIVITY_THRESHOLD}
     * </p>
     * @param matrix the matrix to decompose
     * @throws NonSquareMatrixException if the matrix is not square.
     * @throws NonSymmetricMatrixException if the matrix is not symmetric.
     * @throws NonPositiveDefiniteMatrixException if the matrix is not
     * strictly positive definite.
     * @see #CholeskyDecomposition(RealMatrix, double, double)
     * @see #DEFAULT_RELATIVE_SYMMETRY_THRESHOLD
     * @see #DEFAULT_ABSOLUTE_POSITIVITY_THRESHOLD
     */
    public CholeskyDecomposition(final RealMatrix matrix) {
        this(matrix, DEFAULT_RELATIVE_SYMMETRY_THRESHOLD,
             DEFAULT_ABSOLUTE_POSITIVITY_THRESHOLD);
    }

    /**
     * Calculates the Cholesky decomposition of the given matrix.
     * @param matrix the matrix to decompose
     * @param relativeSymmetryThreshold threshold above which off-diagonal
     * elements are considered too different and matrix not symmetric
     * @param absolutePositivityThreshold threshold below which diagonal
     * elements are considered null and matrix not positive definite
     * @throws NonSquareMatrixException if the matrix is not square.
     * @throws NonSymmetricMatrixException if the matrix is not symmetric.
     * @throws NonPositiveDefiniteMatrixException if the matrix is not
     * strictly positive definite.
     * @see #CholeskyDecomposition(RealMatrix)
     * @see #DEFAULT_RELATIVE_SYMMETRY_THRESHOLD
     * @see #DEFAULT_ABSOLUTE_POSITIVITY_THRESHOLD
     */
    public CholeskyDecomposition(final RealMatrix matrix,
                                     final double relativeSymmetryThreshold,
                                     final double absolutePositivityThreshold) {
        if (!matrix.isSquare()) {
            throw new NonSquareMatrixException(matrix.getRowDimension(),
                                               matrix.getColumnDimension());
        }

        final int order = matrix.getRowDimension();
        lTData   = matrix.getData();
        cachedL  = null;
        cachedLT = null;

        // check the matrix before transformation
        for (int i = 0; i < order; ++i) {
            final double[] lI = lTData[i];

            // check off-diagonal elements (and reset them to 0)
            for (int j = i + 1; j < order; ++j) {
                final double[] lJ = lTData[j];
                final double lIJ = lI[j];
                final double lJI = lJ[i];
                final double maxDelta =
                    relativeSymmetryThreshold * FastMath.max(FastMath.abs(lIJ), FastMath.abs(lJI));
                if (FastMath.abs(lIJ - lJI) > maxDelta) {
                    throw new NonSymmetricMatrixException(i, j, relativeSymmetryThreshold);
                }
                lJ[i] = 0;
           }
        }

        // transform the matrix
        for (int i = 0; i < order; ++i) {

            final double[] ltI = lTData[i];

            // check diagonal element
            if (ltI[i] <= absolutePositivityThreshold) {
                throw new NonPositiveDefiniteMatrixException(ltI[i], i, absolutePositivityThreshold);
            }

            ltI[i] = FastMath.sqrt(ltI[i]);
            final double inverse = 1.0 / ltI[i];

            for (int q = order - 1; q > i; --q) {
                ltI[q] *= inverse;
                final double[] ltQ = lTData[q];
                for (int p = q; p < order; ++p) {
                    ltQ[p] -= ltI[q] * ltI[p];
                }
            }
        }
    }

    /**
     * Returns the matrix L of the decomposition.
     * <p>L is an lower-triangular matrix</p>
     * @return the L matrix
     */
    public RealMatrix getL() {
        if (cachedL == null) {
            cachedL = getLT().transpose();
        }
        return cachedL;
    }

    /**
     * Returns the transpose of the matrix L of the decomposition.
     * <p>L<sup>T</sup> is an upper-triangular matrix</p>
     * @return the transpose of the matrix L of the decomposition
     */
    public RealMatrix getLT() {

        if (cachedLT == null) {
            cachedLT = MatrixUtils.createRealMatrix(lTData);
        }

        // return the cached matrix
        return cachedLT;
    }

    /**
     * Return the determinant of the matrix
     * @return determinant of the matrix
     */
    public double getDeterminant() {
        double determinant = 1.0;
        for (int i = 0; i < lTData.length; ++i) {
            double lTii = lTData[i][i];
            determinant *= lTii * lTii;
        }
        return determinant;
    }

    /**
     * Get a solver for finding the A &times; X = B solution in least square sense.
     * @return a solver
     */
    public DecompositionSolver getSolver() {
        return new Solver(lTData);
    }

    /** Specialized solver. */
    private static class Solver implements DecompositionSolver {
        /** Row-oriented storage for L<sup>T</sup> matrix data. */
        private final double[][] lTData;

        /**
         * Build a solver from decomposed matrix.
         * @param lTData row-oriented storage for L<sup>T</sup> matrix data
         */
        private Solver(final double[][] lTData) {
            this.lTData = lTData;
        }

        /** {@inheritDoc} */
        public boolean isNonSingular() {
            // if we get this far, the matrix was positive definite, hence non-singular
            return true;
        }

        /** {@inheritDoc} */
        public RealVector solve(final RealVector b) {
            final int m = lTData.length;
            if (b.getDimension() != m) {
                throw new DimensionMismatchException(b.getDimension(), m);
            }

            final double[] x = b.toArray();

            // Solve LY = b
            for (int j = 0; j < m; j++) {
                final double[] lJ = lTData[j];
                x[j] /= lJ[j];
                final double xJ = x[j];
                for (int i = j + 1; i < m; i++) {
                    x[i] -= xJ * lJ[i];
                }
            }

            // Solve LTX = Y
            for (int j = m - 1; j >= 0; j--) {
                x[j] /= lTData[j][j];
                final double xJ = x[j];
                for (int i = 0; i < j; i++) {
                    x[i] -= xJ * lTData[i][j];
                }
            }

            return new ArrayRealVector(x, false);
        }

        /** {@inheritDoc} */
        public RealMatrix solve(RealMatrix b) {
            final int m = lTData.length;
            if (b.getRowDimension() != m) {
                throw new DimensionMismatchException(b.getRowDimension(), m);
            }

            final int nColB = b.getColumnDimension();
            final double[][] x = b.getData();

            // Solve LY = b
            for (int j = 0; j < m; j++) {
                final double[] lJ = lTData[j];
                final double lJJ = lJ[j];
                final double[] xJ = x[j];
                for (int k = 0; k < nColB; ++k) {
                    xJ[k] /= lJJ;
                }
                for (int i = j + 1; i < m; i++) {
                    final double[] xI = x[i];
                    final double lJI = lJ[i];
                    for (int k = 0; k < nColB; ++k) {
                        xI[k] -= xJ[k] * lJI;
                    }
                }
            }

            // Solve LTX = Y
            for (int j = m - 1; j >= 0; j--) {
                final double lJJ = lTData[j][j];
                final double[] xJ = x[j];
                for (int k = 0; k < nColB; ++k) {
                    xJ[k] /= lJJ;
                }
                for (int i = 0; i < j; i++) {
                    final double[] xI = x[i];
                    final double lIJ = lTData[i][j];
                    for (int k = 0; k < nColB; ++k) {
                        xI[k] -= xJ[k] * lIJ;
                    }
                }
            }

            return new Array2DRowRealMatrix(x);
        }

        /**
         * Get the inverse of the decomposed matrix.
         *
         * @return the inverse matrix.
         */
        public RealMatrix getInverse() {
            return solve(MatrixUtils.createRealIdentityMatrix(lTData.length));
        }
    }
}
