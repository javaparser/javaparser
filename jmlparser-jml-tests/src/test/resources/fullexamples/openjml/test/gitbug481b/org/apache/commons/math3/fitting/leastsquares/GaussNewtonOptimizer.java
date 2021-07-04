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
package org.apache.commons.math3.fitting.leastsquares;

import org.apache.commons.math3.exception.ConvergenceException;
import org.apache.commons.math3.exception.NullArgumentException;
import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.fitting.leastsquares.LeastSquaresProblem.Evaluation;
import org.apache.commons.math3.linear.ArrayRealVector;
import org.apache.commons.math3.linear.CholeskyDecomposition;
import org.apache.commons.math3.linear.LUDecomposition;
import org.apache.commons.math3.linear.MatrixUtils;
import org.apache.commons.math3.linear.NonPositiveDefiniteMatrixException;
import org.apache.commons.math3.linear.QRDecomposition;
import org.apache.commons.math3.linear.RealMatrix;
import org.apache.commons.math3.linear.RealVector;
import org.apache.commons.math3.linear.SingularMatrixException;
import org.apache.commons.math3.linear.SingularValueDecomposition;
import org.apache.commons.math3.optim.ConvergenceChecker;
import org.apache.commons.math3.util.Incrementor;
import org.apache.commons.math3.util.Pair;

/**
 * Gauss-Newton least-squares solver.
 * <p> This class solve a least-square problem by
 * solving the normal equations of the linearized problem at each iteration. Either LU
 * decomposition or Cholesky decomposition can be used to solve the normal equations,
 * or QR decomposition or SVD decomposition can be used to solve the linear system. LU
 * decomposition is faster but QR decomposition is more robust for difficult problems,
 * and SVD can compute a solution for rank-deficient problems.
 * </p>
 *
 * @since 3.3
 */
public class GaussNewtonOptimizer implements LeastSquaresOptimizer {

    /** The decomposition algorithm to use to solve the normal equations. */
    //TODO move to linear package and expand options?
    public enum Decomposition {
        /**
         * Solve by forming the normal equations (J<sup>T</sup>Jx=J<sup>T</sup>r) and
         * using the {@link LUDecomposition}.
         *
         * <p> Theoretically this method takes mn<sup>2</sup>/2 operations to compute the
         * normal matrix and n<sup>3</sup>/3 operations (m > n) to solve the system using
         * the LU decomposition. </p>
         */
        LU {
            @Override
            protected RealVector solve(final RealMatrix jacobian,
                                       final RealVector residuals) {
                try {
                    final Pair<RealMatrix, RealVector> normalEquation =
                            computeNormalMatrix(jacobian, residuals);
                    final RealMatrix normal = normalEquation.getFirst();
                    final RealVector jTr = normalEquation.getSecond();
                    return new LUDecomposition(normal, SINGULARITY_THRESHOLD)
                            .getSolver()
                            .solve(jTr);
                } catch (SingularMatrixException e) {
                    throw new ConvergenceException(LocalizedFormats.UNABLE_TO_SOLVE_SINGULAR_PROBLEM, e);
                }
            }
        },
        /**
         * Solve the linear least squares problem (Jx=r) using the {@link
         * QRDecomposition}.
         *
         * <p> Theoretically this method takes mn<sup>2</sup> - n<sup>3</sup>/3 operations
         * (m > n) and has better numerical accuracy than any method that forms the normal
         * equations. </p>
         */
        QR {
            @Override
            protected RealVector solve(final RealMatrix jacobian,
                                       final RealVector residuals) {
                try {
                    return new QRDecomposition(jacobian, SINGULARITY_THRESHOLD)
                            .getSolver()
                            .solve(residuals);
                } catch (SingularMatrixException e) {
                    throw new ConvergenceException(LocalizedFormats.UNABLE_TO_SOLVE_SINGULAR_PROBLEM, e);
                }
            }
        },
        /**
         * Solve by forming the normal equations (J<sup>T</sup>Jx=J<sup>T</sup>r) and
         * using the {@link CholeskyDecomposition}.
         *
         * <p> Theoretically this method takes mn<sup>2</sup>/2 operations to compute the
         * normal matrix and n<sup>3</sup>/6 operations (m > n) to solve the system using
         * the Cholesky decomposition. </p>
         */
        CHOLESKY {
            @Override
            protected RealVector solve(final RealMatrix jacobian,
                                       final RealVector residuals) {
                try {
                    final Pair<RealMatrix, RealVector> normalEquation =
                            computeNormalMatrix(jacobian, residuals);
                    final RealMatrix normal = normalEquation.getFirst();
                    final RealVector jTr = normalEquation.getSecond();
                    return new CholeskyDecomposition(
                            normal, SINGULARITY_THRESHOLD, SINGULARITY_THRESHOLD)
                            .getSolver()
                            .solve(jTr);
                } catch (NonPositiveDefiniteMatrixException e) {
                    throw new ConvergenceException(LocalizedFormats.UNABLE_TO_SOLVE_SINGULAR_PROBLEM, e);
                }
            }
        },
        /**
         * Solve the linear least squares problem using the {@link
         * SingularValueDecomposition}.
         *
         * <p> This method is slower, but can provide a solution for rank deficient and
         * nearly singular systems.
         */
        SVD {
            @Override
            protected RealVector solve(final RealMatrix jacobian,
                                       final RealVector residuals) {
                return new SingularValueDecomposition(jacobian)
                        .getSolver()
                        .solve(residuals);
            }
        };

        /**
         * Solve the linear least squares problem Jx=r.
         *
         * @param jacobian  the Jacobian matrix, J. the number of rows >= the number or
         *                  columns.
         * @param residuals the computed residuals, r.
         * @return the solution x, to the linear least squares problem Jx=r.
         * @throws ConvergenceException if the matrix properties (e.g. singular) do not
         *                              permit a solution.
         */
        protected abstract RealVector solve(RealMatrix jacobian,
                                            RealVector residuals);
    }

    /**
     * The singularity threshold for matrix decompositions. Determines when a {@link
     * ConvergenceException} is thrown. The current value was the default value for {@link
     * LUDecomposition}.
     */
    private static final double SINGULARITY_THRESHOLD = 1e-11;

    /** Indicator for using LU decomposition. */
    private final Decomposition decomposition;

    /**
     * Creates a Gauss Newton optimizer.
     * <p/>
     * The default for the algorithm is to solve the normal equations using QR
     * decomposition.
     */
    public GaussNewtonOptimizer() {
        this(Decomposition.QR);
    }

    /**
     * Create a Gauss Newton optimizer that uses the given decomposition algorithm to
     * solve the normal equations.
     *
     * @param decomposition the {@link Decomposition} algorithm.
     */
    public GaussNewtonOptimizer(final Decomposition decomposition) {
        this.decomposition = decomposition;
    }

    /**
     * Get the matrix decomposition algorithm used to solve the normal equations.
     *
     * @return the matrix {@link Decomposition} algoritm.
     */
    public Decomposition getDecomposition() {
        return this.decomposition;
    }

    /**
     * Configure the decomposition algorithm.
     *
     * @param newDecomposition the {@link Decomposition} algorithm to use.
     * @return a new instance.
     */
    public GaussNewtonOptimizer withDecomposition(final Decomposition newDecomposition) {
        return new GaussNewtonOptimizer(newDecomposition);
    }

    /** {@inheritDoc} */
    public Optimum optimize(final LeastSquaresProblem lsp) {
        //create local evaluation and iteration counts
        final Incrementor evaluationCounter = lsp.getEvaluationCounter();
        final Incrementor iterationCounter = lsp.getIterationCounter();
        final ConvergenceChecker<Evaluation> checker
                = lsp.getConvergenceChecker();

        // Computation will be useless without a checker (see "for-loop").
        if (checker == null) {
            throw new NullArgumentException();
        }

        RealVector currentPoint = lsp.getStart();

        // iterate until convergence is reached
        Evaluation current = null;
        while (true) {
            iterationCounter.incrementCount();

            // evaluate the objective function and its jacobian
            Evaluation previous = current;
            // Value of the objective function at "currentPoint".
            evaluationCounter.incrementCount();
            current = lsp.evaluate(currentPoint);
            final RealVector currentResiduals = current.getResiduals();
            final RealMatrix weightedJacobian = current.getJacobian();
            currentPoint = current.getPoint();

            // Check convergence.
            if (previous != null &&
                checker.converged(iterationCounter.getCount(), previous, current)) {
                return new OptimumImpl(current,
                                       evaluationCounter.getCount(),
                                       iterationCounter.getCount());
            }

            // solve the linearized least squares problem
            final RealVector dX = this.decomposition.solve(weightedJacobian, currentResiduals);
            // update the estimated parameters
            currentPoint = currentPoint.add(dX);
        }
    }

    /** {@inheritDoc} */
    @Override
    public String toString() {
        return "GaussNewtonOptimizer{" +
                "decomposition=" + decomposition +
                '}';
    }

    /**
     * Compute the normal matrix, J<sup>T</sup>J.
     *
     * @param jacobian  the m by n jacobian matrix, J. Input.
     * @param residuals the m by 1 residual vector, r. Input.
     * @return  the n by n normal matrix and  the n by 1 J<sup>Tr vector.
     */
    private static Pair<RealMatrix, RealVector> computeNormalMatrix(final RealMatrix jacobian,
                                                                    final RealVector residuals) {
        //since the normal matrix is symmetric, we only need to compute half of it.
        final int nR = jacobian.getRowDimension();
        final int nC = jacobian.getColumnDimension();
        //allocate space for return values
        final RealMatrix normal = MatrixUtils.createRealMatrix(nC, nC);
        final RealVector jTr = new ArrayRealVector(nC);
        //for each measurement
        for (int i = 0; i < nR; ++i) {
            //compute JTr for measurement i
            for (int j = 0; j < nC; j++) {
                jTr.setEntry(j, jTr.getEntry(j) +
                        residuals.getEntry(i) * jacobian.getEntry(i, j));
            }

            // add the the contribution to the normal matrix for measurement i
            for (int k = 0; k < nC; ++k) {
                //only compute the upper triangular part
                for (int l = k; l < nC; ++l) {
                    normal.setEntry(k, l, normal.getEntry(k, l) +
                            jacobian.getEntry(i, k) * jacobian.getEntry(i, l));
                }
            }
        }
        //copy the upper triangular part to the lower triangular part.
        for (int i = 0; i < nC; i++) {
            for (int j = 0; j < i; j++) {
                normal.setEntry(i, j, normal.getEntry(j, i));
            }
        }
        return new Pair<RealMatrix, RealVector>(normal, jTr);
    }

}
