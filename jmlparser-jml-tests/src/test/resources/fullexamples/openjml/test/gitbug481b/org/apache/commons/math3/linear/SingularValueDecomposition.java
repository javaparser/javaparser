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

import org.apache.commons.math3.exception.NumberIsTooLargeException;
import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.util.FastMath;
import org.apache.commons.math3.util.Precision;

/**
 * Calculates the compact Singular Value Decomposition of a matrix.
 * <p>
 * The Singular Value Decomposition of matrix A is a set of three matrices: U,
 * &Sigma; and V such that A = U &times; &Sigma; &times; V<sup>T</sup>. Let A be
 * a m &times; n matrix, then U is a m &times; p orthogonal matrix, &Sigma; is a
 * p &times; p diagonal matrix with positive or null elements, V is a p &times;
 * n orthogonal matrix (hence V<sup>T</sup> is also orthogonal) where
 * p=min(m,n).
 * </p>
 * <p>This class is similar to the class with similar name from the
 * <a href="http://math.nist.gov/javanumerics/jama/">JAMA</a> library, with the
 * following changes:</p>
 * <ul>
 *   <li>the {@code norm2} method which has been renamed as {@link #getNorm()
 *   getNorm},</li>
 *   <li>the {@code cond} method which has been renamed as {@link
 *   #getConditionNumber() getConditionNumber},</li>
 *   <li>the {@code rank} method which has been renamed as {@link #getRank()
 *   getRank},</li>
 *   <li>a {@link #getUT() getUT} method has been added,</li>
 *   <li>a {@link #getVT() getVT} method has been added,</li>
 *   <li>a {@link #getSolver() getSolver} method has been added,</li>
 *   <li>a {@link #getCovariance(double) getCovariance} method has been added.</li>
 * </ul>
 * @see <a href="http://mathworld.wolfram.com/SingularValueDecomposition.html">MathWorld</a>
 * @see <a href="http://en.wikipedia.org/wiki/Singular_value_decomposition">Wikipedia</a>
 * @since 2.0 (changed to concrete class in 3.0)
 */
public class SingularValueDecomposition {
    /** Relative threshold for small singular values. */
    private static final double EPS = 0x1.0p-52;
    /** Absolute threshold for small singular values. */
    private static final double TINY = 0x1.0p-966;
    /** Computed singular values. */
    private final double[] singularValues;
    /** max(row dimension, column dimension). */
    private final int m;
    /** min(row dimension, column dimension). */
    private final int n;
    /** Indicator for transposed matrix. */
    private final boolean transposed;
    /** Cached value of U matrix. */
    private final RealMatrix cachedU;
    /** Cached value of transposed U matrix. */
    private RealMatrix cachedUt;
    /** Cached value of S (diagonal) matrix. */
    private RealMatrix cachedS;
    /** Cached value of V matrix. */
    private final RealMatrix cachedV;
    /** Cached value of transposed V matrix. */
    private RealMatrix cachedVt;
    /**
     * Tolerance value for small singular values, calculated once we have
     * populated "singularValues".
     **/
    private final double tol;

    /**
     * Calculates the compact Singular Value Decomposition of the given matrix.
     *
     * @param matrix Matrix to decompose.
     */
    public SingularValueDecomposition(final RealMatrix matrix) {
        final double[][] A;

         // "m" is always the largest dimension.
        if (matrix.getRowDimension() < matrix.getColumnDimension()) {
            transposed = true;
            A = matrix.transpose().getData();
            m = matrix.getColumnDimension();
            n = matrix.getRowDimension();
        } else {
            transposed = false;
            A = matrix.getData();
            m = matrix.getRowDimension();
            n = matrix.getColumnDimension();
        }

        singularValues = new double[n];
        final double[][] U = new double[m][n];
        final double[][] V = new double[n][n];
        final double[] e = new double[n];
        final double[] work = new double[m];
        // Reduce A to bidiagonal form, storing the diagonal elements
        // in s and the super-diagonal elements in e.
        final int nct = FastMath.min(m - 1, n);
        final int nrt = FastMath.max(0, n - 2);
        for (int k = 0; k < FastMath.max(nct, nrt); k++) {
            if (k < nct) {
                // Compute the transformation for the k-th column and
                // place the k-th diagonal in s[k].
                // Compute 2-norm of k-th column without under/overflow.
                singularValues[k] = 0;
                for (int i = k; i < m; i++) {
                    singularValues[k] = FastMath.hypot(singularValues[k], A[i][k]);
                }
                if (singularValues[k] != 0) {
                    if (A[k][k] < 0) {
                        singularValues[k] = -singularValues[k];
                    }
                    for (int i = k; i < m; i++) {
                        A[i][k] /= singularValues[k];
                    }
                    A[k][k] += 1;
                }
                singularValues[k] = -singularValues[k];
            }
            for (int j = k + 1; j < n; j++) {
                if (k < nct &&
                    singularValues[k] != 0) {
                    // Apply the transformation.
                    double t = 0;
                    for (int i = k; i < m; i++) {
                        t += A[i][k] * A[i][j];
                    }
                    t = -t / A[k][k];
                    for (int i = k; i < m; i++) {
                        A[i][j] += t * A[i][k];
                    }
                }
                // Place the k-th row of A into e for the
                // subsequent calculation of the row transformation.
                e[j] = A[k][j];
            }
            if (k < nct) {
                // Place the transformation in U for subsequent back
                // multiplication.
                for (int i = k; i < m; i++) {
                    U[i][k] = A[i][k];
                }
            }
            if (k < nrt) {
                // Compute the k-th row transformation and place the
                // k-th super-diagonal in e[k].
                // Compute 2-norm without under/overflow.
                e[k] = 0;
                for (int i = k + 1; i < n; i++) {
                    e[k] = FastMath.hypot(e[k], e[i]);
                }
                if (e[k] != 0) {
                    if (e[k + 1] < 0) {
                        e[k] = -e[k];
                    }
                    for (int i = k + 1; i < n; i++) {
                        e[i] /= e[k];
                    }
                    e[k + 1] += 1;
                }
                e[k] = -e[k];
                if (k + 1 < m &&
                    e[k] != 0) {
                    // Apply the transformation.
                    for (int i = k + 1; i < m; i++) {
                        work[i] = 0;
                    }
                    for (int j = k + 1; j < n; j++) {
                        for (int i = k + 1; i < m; i++) {
                            work[i] += e[j] * A[i][j];
                        }
                    }
                    for (int j = k + 1; j < n; j++) {
                        final double t = -e[j] / e[k + 1];
                        for (int i = k + 1; i < m; i++) {
                            A[i][j] += t * work[i];
                        }
                    }
                }

                // Place the transformation in V for subsequent
                // back multiplication.
                for (int i = k + 1; i < n; i++) {
                    V[i][k] = e[i];
                }
            }
        }
        // Set up the final bidiagonal matrix or order p.
        int p = n;
        if (nct < n) {
            singularValues[nct] = A[nct][nct];
        }
        if (m < p) {
            singularValues[p - 1] = 0;
        }
        if (nrt + 1 < p) {
            e[nrt] = A[nrt][p - 1];
        }
        e[p - 1] = 0;

        // Generate U.
        for (int j = nct; j < n; j++) {
            for (int i = 0; i < m; i++) {
                U[i][j] = 0;
            }
            U[j][j] = 1;
        }
        for (int k = nct - 1; k >= 0; k--) {
            if (singularValues[k] != 0) {
                for (int j = k + 1; j < n; j++) {
                    double t = 0;
                    for (int i = k; i < m; i++) {
                        t += U[i][k] * U[i][j];
                    }
                    t = -t / U[k][k];
                    for (int i = k; i < m; i++) {
                        U[i][j] += t * U[i][k];
                    }
                }
                for (int i = k; i < m; i++) {
                    U[i][k] = -U[i][k];
                }
                U[k][k] = 1 + U[k][k];
                for (int i = 0; i < k - 1; i++) {
                    U[i][k] = 0;
                }
            } else {
                for (int i = 0; i < m; i++) {
                    U[i][k] = 0;
                }
                U[k][k] = 1;
            }
        }

        // Generate V.
        for (int k = n - 1; k >= 0; k--) {
            if (k < nrt &&
                e[k] != 0) {
                for (int j = k + 1; j < n; j++) {
                    double t = 0;
                    for (int i = k + 1; i < n; i++) {
                        t += V[i][k] * V[i][j];
                    }
                    t = -t / V[k + 1][k];
                    for (int i = k + 1; i < n; i++) {
                        V[i][j] += t * V[i][k];
                    }
                }
            }
            for (int i = 0; i < n; i++) {
                V[i][k] = 0;
            }
            V[k][k] = 1;
        }

        // Main iteration loop for the singular values.
        final int pp = p - 1;
        while (p > 0) {
            int k;
            int kase;
            // Here is where a test for too many iterations would go.
            // This section of the program inspects for
            // negligible elements in the s and e arrays.  On
            // completion the variables kase and k are set as follows.
            // kase = 1     if s(p) and e[k-1] are negligible and k<p
            // kase = 2     if s(k) is negligible and k<p
            // kase = 3     if e[k-1] is negligible, k<p, and
            //              s(k), ..., s(p) are not negligible (qr step).
            // kase = 4     if e(p-1) is negligible (convergence).
            for (k = p - 2; k >= 0; k--) {
                final double threshold
                    = TINY + EPS * (FastMath.abs(singularValues[k]) +
                                    FastMath.abs(singularValues[k + 1]));

                // the following condition is written this way in order
                // to break out of the loop when NaN occurs, writing it
                // as "if (FastMath.abs(e[k]) <= threshold)" would loop
                // indefinitely in case of NaNs because comparison on NaNs
                // always return false, regardless of what is checked
                // see issue MATH-947
                if (!(FastMath.abs(e[k]) > threshold)) {
                    e[k] = 0;
                    break;
                }

            }

            if (k == p - 2) {
                kase = 4;
            } else {
                int ks;
                for (ks = p - 1; ks >= k; ks--) {
                    if (ks == k) {
                        break;
                    }
                    final double t = (ks != p ? FastMath.abs(e[ks]) : 0) +
                        (ks != k + 1 ? FastMath.abs(e[ks - 1]) : 0);
                    if (FastMath.abs(singularValues[ks]) <= TINY + EPS * t) {
                        singularValues[ks] = 0;
                        break;
                    }
                }
                if (ks == k) {
                    kase = 3;
                } else if (ks == p - 1) {
                    kase = 1;
                } else {
                    kase = 2;
                    k = ks;
                }
            }
            k++;
            // Perform the task indicated by kase.
            switch (kase) {
                // Deflate negligible s(p).
                case 1: {
                    double f = e[p - 2];
                    e[p - 2] = 0;
                    for (int j = p - 2; j >= k; j--) {
                        double t = FastMath.hypot(singularValues[j], f);
                        final double cs = singularValues[j] / t;
                        final double sn = f / t;
                        singularValues[j] = t;
                        if (j != k) {
                            f = -sn * e[j - 1];
                            e[j - 1] = cs * e[j - 1];
                        }

                        for (int i = 0; i < n; i++) {
                            t = cs * V[i][j] + sn * V[i][p - 1];
                            V[i][p - 1] = -sn * V[i][j] + cs * V[i][p - 1];
                            V[i][j] = t;
                        }
                    }
                }
                break;
                // Split at negligible s(k).
                case 2: {
                    double f = e[k - 1];
                    e[k - 1] = 0;
                    for (int j = k; j < p; j++) {
                        double t = FastMath.hypot(singularValues[j], f);
                        final double cs = singularValues[j] / t;
                        final double sn = f / t;
                        singularValues[j] = t;
                        f = -sn * e[j];
                        e[j] = cs * e[j];

                        for (int i = 0; i < m; i++) {
                            t = cs * U[i][j] + sn * U[i][k - 1];
                            U[i][k - 1] = -sn * U[i][j] + cs * U[i][k - 1];
                            U[i][j] = t;
                        }
                    }
                }
                break;
                // Perform one qr step.
                case 3: {
                    // Calculate the shift.
                    final double maxPm1Pm2 = FastMath.max(FastMath.abs(singularValues[p - 1]),
                                                          FastMath.abs(singularValues[p - 2]));
                    final double scale = FastMath.max(FastMath.max(FastMath.max(maxPm1Pm2,
                                                                                FastMath.abs(e[p - 2])),
                                                                   FastMath.abs(singularValues[k])),
                                                      FastMath.abs(e[k]));
                    final double sp = singularValues[p - 1] / scale;
                    final double spm1 = singularValues[p - 2] / scale;
                    final double epm1 = e[p - 2] / scale;
                    final double sk = singularValues[k] / scale;
                    final double ek = e[k] / scale;
                    final double b = ((spm1 + sp) * (spm1 - sp) + epm1 * epm1) / 2.0;
                    final double c = (sp * epm1) * (sp * epm1);
                    double shift = 0;
                    if (b != 0 ||
                        c != 0) {
                        shift = FastMath.sqrt(b * b + c);
                        if (b < 0) {
                            shift = -shift;
                        }
                        shift = c / (b + shift);
                    }
                    double f = (sk + sp) * (sk - sp) + shift;
                    double g = sk * ek;
                    // Chase zeros.
                    for (int j = k; j < p - 1; j++) {
                        double t = FastMath.hypot(f, g);
                        double cs = f / t;
                        double sn = g / t;
                        if (j != k) {
                            e[j - 1] = t;
                        }
                        f = cs * singularValues[j] + sn * e[j];
                        e[j] = cs * e[j] - sn * singularValues[j];
                        g = sn * singularValues[j + 1];
                        singularValues[j + 1] = cs * singularValues[j + 1];

                        for (int i = 0; i < n; i++) {
                            t = cs * V[i][j] + sn * V[i][j + 1];
                            V[i][j + 1] = -sn * V[i][j] + cs * V[i][j + 1];
                            V[i][j] = t;
                        }
                        t = FastMath.hypot(f, g);
                        cs = f / t;
                        sn = g / t;
                        singularValues[j] = t;
                        f = cs * e[j] + sn * singularValues[j + 1];
                        singularValues[j + 1] = -sn * e[j] + cs * singularValues[j + 1];
                        g = sn * e[j + 1];
                        e[j + 1] = cs * e[j + 1];
                        if (j < m - 1) {
                            for (int i = 0; i < m; i++) {
                                t = cs * U[i][j] + sn * U[i][j + 1];
                                U[i][j + 1] = -sn * U[i][j] + cs * U[i][j + 1];
                                U[i][j] = t;
                            }
                        }
                    }
                    e[p - 2] = f;
                }
                break;
                // Convergence.
                default: {
                    // Make the singular values positive.
                    if (singularValues[k] <= 0) {
                        singularValues[k] = singularValues[k] < 0 ? -singularValues[k] : 0;

                        for (int i = 0; i <= pp; i++) {
                            V[i][k] = -V[i][k];
                        }
                    }
                    // Order the singular values.
                    while (k < pp) {
                        if (singularValues[k] >= singularValues[k + 1]) {
                            break;
                        }
                        double t = singularValues[k];
                        singularValues[k] = singularValues[k + 1];
                        singularValues[k + 1] = t;
                        if (k < n - 1) {
                            for (int i = 0; i < n; i++) {
                                t = V[i][k + 1];
                                V[i][k + 1] = V[i][k];
                                V[i][k] = t;
                            }
                        }
                        if (k < m - 1) {
                            for (int i = 0; i < m; i++) {
                                t = U[i][k + 1];
                                U[i][k + 1] = U[i][k];
                                U[i][k] = t;
                            }
                        }
                        k++;
                    }
                    p--;
                }
                break;
            }
        }

        // Set the small value tolerance used to calculate rank and pseudo-inverse
        tol = FastMath.max(m * singularValues[0] * EPS,
                           FastMath.sqrt(Precision.SAFE_MIN));

        if (!transposed) {
            cachedU = MatrixUtils.createRealMatrix(U);
            cachedV = MatrixUtils.createRealMatrix(V);
        } else {
            cachedU = MatrixUtils.createRealMatrix(V);
            cachedV = MatrixUtils.createRealMatrix(U);
        }
    }

    /**
     * Returns the matrix U of the decomposition.
     * <p>U is an orthogonal matrix, i.e. its transpose is also its inverse.</p>
     * @return the U matrix
     * @see #getUT()
     */
    public RealMatrix getU() {
        // return the cached matrix
        return cachedU;

    }

    /**
     * Returns the transpose of the matrix U of the decomposition.
     * <p>U is an orthogonal matrix, i.e. its transpose is also its inverse.</p>
     * @return the U matrix (or null if decomposed matrix is singular)
     * @see #getU()
     */
    public RealMatrix getUT() {
        if (cachedUt == null) {
            cachedUt = getU().transpose();
        }
        // return the cached matrix
        return cachedUt;
    }

    /**
     * Returns the diagonal matrix &Sigma; of the decomposition.
     * <p>&Sigma; is a diagonal matrix. The singular values are provided in
     * non-increasing order, for compatibility with Jama.</p>
     * @return the &Sigma; matrix
     */
    public RealMatrix getS() {
        if (cachedS == null) {
            // cache the matrix for subsequent calls
            cachedS = MatrixUtils.createRealDiagonalMatrix(singularValues);
        }
        return cachedS;
    }

    /**
     * Returns the diagonal elements of the matrix &Sigma; of the decomposition.
     * <p>The singular values are provided in non-increasing order, for
     * compatibility with Jama.</p>
     * @return the diagonal elements of the &Sigma; matrix
     */
    public double[] getSingularValues() {
        return singularValues.clone();
    }

    /**
     * Returns the matrix V of the decomposition.
     * <p>V is an orthogonal matrix, i.e. its transpose is also its inverse.</p>
     * @return the V matrix (or null if decomposed matrix is singular)
     * @see #getVT()
     */
    public RealMatrix getV() {
        // return the cached matrix
        return cachedV;
    }

    /**
     * Returns the transpose of the matrix V of the decomposition.
     * <p>V is an orthogonal matrix, i.e. its transpose is also its inverse.</p>
     * @return the V matrix (or null if decomposed matrix is singular)
     * @see #getV()
     */
    public RealMatrix getVT() {
        if (cachedVt == null) {
            cachedVt = getV().transpose();
        }
        // return the cached matrix
        return cachedVt;
    }

    /**
     * Returns the n &times; n covariance matrix.
     * <p>The covariance matrix is V &times; J &times; V<sup>T</sup>
     * where J is the diagonal matrix of the inverse of the squares of
     * the singular values.</p>
     * @param minSingularValue value below which singular values are ignored
     * (a 0 or negative value implies all singular value will be used)
     * @return covariance matrix
     * @exception IllegalArgumentException if minSingularValue is larger than
     * the largest singular value, meaning all singular values are ignored
     */
    public RealMatrix getCovariance(final double minSingularValue) {
        // get the number of singular values to consider
        final int p = singularValues.length;
        int dimension = 0;
        while (dimension < p &&
               singularValues[dimension] >= minSingularValue) {
            ++dimension;
        }

        if (dimension == 0) {
            throw new NumberIsTooLargeException(LocalizedFormats.TOO_LARGE_CUTOFF_SINGULAR_VALUE,
                                                minSingularValue, singularValues[0], true);
        }

        final double[][] data = new double[dimension][p];
        getVT().walkInOptimizedOrder(new DefaultRealMatrixPreservingVisitor() {
            /** {@inheritDoc} */
            @Override
            public void visit(final int row, final int column,
                    final double value) {
                data[row][column] = value / singularValues[row];
            }
        }, 0, dimension - 1, 0, p - 1);

        RealMatrix jv = new Array2DRowRealMatrix(data, false);
        return jv.transpose().multiply(jv);
    }

    /**
     * Returns the L<sub>2</sub> norm of the matrix.
     * <p>The L<sub>2</sub> norm is max(|A &times; u|<sub>2</sub> /
     * |u|<sub>2</sub>), where |.|<sub>2</sub> denotes the vectorial 2-norm
     * (i.e. the traditional euclidian norm).</p>
     * @return norm
     */
    public double getNorm() {
        return singularValues[0];
    }

    /**
     * Return the condition number of the matrix.
     * @return condition number of the matrix
     */
    public double getConditionNumber() {
        return singularValues[0] / singularValues[n - 1];
    }

    /**
     * Computes the inverse of the condition number.
     * In cases of rank deficiency, the {@link #getConditionNumber() condition
     * number} will become undefined.
     *
     * @return the inverse of the condition number.
     */
    public double getInverseConditionNumber() {
        return singularValues[n - 1] / singularValues[0];
    }

    /**
     * Return the effective numerical matrix rank.
     * <p>The effective numerical rank is the number of non-negligible
     * singular values. The threshold used to identify non-negligible
     * terms is max(m,n) &times; ulp(s<sub>1</sub>) where ulp(s<sub>1</sub>)
     * is the least significant bit of the largest singular value.</p>
     * @return effective numerical matrix rank
     */
    public int getRank() {
        int r = 0;
        for (int i = 0; i < singularValues.length; i++) {
            if (singularValues[i] > tol) {
                r++;
            }
        }
        return r;
    }

    /**
     * Get a solver for finding the A &times; X = B solution in least square sense.
     * @return a solver
     */
    public DecompositionSolver getSolver() {
        return new Solver(singularValues, getUT(), getV(), getRank() == m, tol);
    }

    /** Specialized solver. */
    private static class Solver implements DecompositionSolver {
        /** Pseudo-inverse of the initial matrix. */
        private final RealMatrix pseudoInverse;
        /** Singularity indicator. */
        private boolean nonSingular;

        /**
         * Build a solver from decomposed matrix.
         *
         * @param singularValues Singular values.
         * @param uT U<sup>T</sup> matrix of the decomposition.
         * @param v V matrix of the decomposition.
         * @param nonSingular Singularity indicator.
         * @param tol tolerance for singular values
         */
        private Solver(final double[] singularValues, final RealMatrix uT,
                       final RealMatrix v, final boolean nonSingular, final double tol) {
            final double[][] suT = uT.getData();
            for (int i = 0; i < singularValues.length; ++i) {
                final double a;
                if (singularValues[i] > tol) {
                    a = 1 / singularValues[i];
                } else {
                    a = 0;
                }
                final double[] suTi = suT[i];
                for (int j = 0; j < suTi.length; ++j) {
                    suTi[j] *= a;
                }
            }
            pseudoInverse = v.multiply(new Array2DRowRealMatrix(suT, false));
            this.nonSingular = nonSingular;
        }

        /**
         * Solve the linear equation A &times; X = B in least square sense.
         * <p>
         * The m&times;n matrix A may not be square, the solution X is such that
         * ||A &times; X - B|| is minimal.
         * </p>
         * @param b Right-hand side of the equation A &times; X = B
         * @return a vector X that minimizes the two norm of A &times; X - B
         * @throws org.apache.commons.math3.exception.DimensionMismatchException
         * if the matrices dimensions do not match.
         */
        public RealVector solve(final RealVector b) {
            return pseudoInverse.operate(b);
        }

        /**
         * Solve the linear equation A &times; X = B in least square sense.
         * <p>
         * The m&times;n matrix A may not be square, the solution X is such that
         * ||A &times; X - B|| is minimal.
         * </p>
         *
         * @param b Right-hand side of the equation A &times; X = B
         * @return a matrix X that minimizes the two norm of A &times; X - B
         * @throws org.apache.commons.math3.exception.DimensionMismatchException
         * if the matrices dimensions do not match.
         */
        public RealMatrix solve(final RealMatrix b) {
            return pseudoInverse.multiply(b);
        }

        /**
         * Check if the decomposed matrix is non-singular.
         *
         * @return {@code true} if the decomposed matrix is non-singular.
         */
        public boolean isNonSingular() {
            return nonSingular;
        }

        /**
         * Get the pseudo-inverse of the decomposed matrix.
         *
         * @return the inverse matrix.
         */
        public RealMatrix getInverse() {
            return pseudoInverse;
        }
    }
}
