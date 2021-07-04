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

import org.apache.commons.math3.exception.MathIllegalStateException;
import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.analysis.MultivariateMatrixFunction;
import org.apache.commons.math3.analysis.MultivariateVectorFunction;
import org.apache.commons.math3.fitting.leastsquares.LeastSquaresProblem.Evaluation;
import org.apache.commons.math3.linear.Array2DRowRealMatrix;
import org.apache.commons.math3.linear.ArrayRealVector;
import org.apache.commons.math3.linear.DiagonalMatrix;
import org.apache.commons.math3.linear.EigenDecomposition;
import org.apache.commons.math3.linear.RealMatrix;
import org.apache.commons.math3.linear.RealVector;
import org.apache.commons.math3.optim.AbstractOptimizationProblem;
import org.apache.commons.math3.optim.ConvergenceChecker;
import org.apache.commons.math3.optim.PointVectorValuePair;
import org.apache.commons.math3.util.FastMath;
import org.apache.commons.math3.util.Incrementor;
import org.apache.commons.math3.util.Pair;

/**
 * A Factory for creating {@link LeastSquaresProblem}s.
 *
 * @since 3.3
 */
public class LeastSquaresFactory {

    /** Prevent instantiation. */
    private LeastSquaresFactory() {}

    /**
     * Create a {@link org.apache.commons.math3.fitting.leastsquares.LeastSquaresProblem}
     * from the given elements. There will be no weights applied (unit weights).
     *
     * @param model          the model function. Produces the computed values.
     * @param observed       the observed (target) values
     * @param start          the initial guess.
     * @param weight         the weight matrix
     * @param checker        convergence checker
     * @param maxEvaluations the maximum number of times to evaluate the model
     * @param maxIterations  the maximum number to times to iterate in the algorithm
     * @param lazyEvaluation Whether the call to {@link Evaluation#evaluate(RealVector)}
     * will defer the evaluation until access to the value is requested.
     * @param paramValidator Model parameters validator.
     * @return the specified General Least Squares problem.
     *
     * @since 3.4
     */
    public static LeastSquaresProblem create(final MultivariateJacobianFunction model,
                                             final RealVector observed,
                                             final RealVector start,
                                             final RealMatrix weight,
                                             final ConvergenceChecker<Evaluation> checker,
                                             final int maxEvaluations,
                                             final int maxIterations,
                                             final boolean lazyEvaluation,
                                             final ParameterValidator paramValidator) {
        final LeastSquaresProblem p = new LocalLeastSquaresProblem(model,
                                                                   observed,
                                                                   start,
                                                                   checker,
                                                                   maxEvaluations,
                                                                   maxIterations,
                                                                   lazyEvaluation,
                                                                   paramValidator);
        if (weight != null) {
            return weightMatrix(p, weight);
        } else {
            return p;
        }
    }

    /**
     * Create a {@link org.apache.commons.math3.fitting.leastsquares.LeastSquaresProblem}
     * from the given elements. There will be no weights applied (unit weights).
     *
     * @param model          the model function. Produces the computed values.
     * @param observed       the observed (target) values
     * @param start          the initial guess.
     * @param checker        convergence checker
     * @param maxEvaluations the maximum number of times to evaluate the model
     * @param maxIterations  the maximum number to times to iterate in the algorithm
     * @return the specified General Least Squares problem.
     */
    public static LeastSquaresProblem create(final MultivariateJacobianFunction model,
                                             final RealVector observed,
                                             final RealVector start,
                                             final ConvergenceChecker<Evaluation> checker,
                                             final int maxEvaluations,
                                             final int maxIterations) {
        return create(model,
                      observed,
                      start,
                      null,
                      checker,
                      maxEvaluations,
                      maxIterations,
                      false,
                      null);
    }

    /**
     * Create a {@link org.apache.commons.math3.fitting.leastsquares.LeastSquaresProblem}
     * from the given elements.
     *
     * @param model          the model function. Produces the computed values.
     * @param observed       the observed (target) values
     * @param start          the initial guess.
     * @param weight         the weight matrix
     * @param checker        convergence checker
     * @param maxEvaluations the maximum number of times to evaluate the model
     * @param maxIterations  the maximum number to times to iterate in the algorithm
     * @return the specified General Least Squares problem.
     */
    public static LeastSquaresProblem create(final MultivariateJacobianFunction model,
                                             final RealVector observed,
                                             final RealVector start,
                                             final RealMatrix weight,
                                             final ConvergenceChecker<Evaluation> checker,
                                             final int maxEvaluations,
                                             final int maxIterations) {
        return weightMatrix(create(model,
                                   observed,
                                   start,
                                   checker,
                                   maxEvaluations,
                                   maxIterations),
                            weight);
    }

    /**
     * Create a {@link org.apache.commons.math3.fitting.leastsquares.LeastSquaresProblem}
     * from the given elements.
     * <p>
     * This factory method is provided for continuity with previous interfaces. Newer
     * applications should use {@link #create(MultivariateJacobianFunction, RealVector,
     * RealVector, ConvergenceChecker, int, int)}, or {@link #create(MultivariateJacobianFunction,
     * RealVector, RealVector, RealMatrix, ConvergenceChecker, int, int)}.
     *
     * @param model          the model function. Produces the computed values.
     * @param jacobian       the jacobian of the model with respect to the parameters
     * @param observed       the observed (target) values
     * @param start          the initial guess.
     * @param weight         the weight matrix
     * @param checker        convergence checker
     * @param maxEvaluations the maximum number of times to evaluate the model
     * @param maxIterations  the maximum number to times to iterate in the algorithm
     * @return the specified General Least Squares problem.
     */
    public static LeastSquaresProblem create(final MultivariateVectorFunction model,
                                             final MultivariateMatrixFunction jacobian,
                                             final double[] observed,
                                             final double[] start,
                                             final RealMatrix weight,
                                             final ConvergenceChecker<Evaluation> checker,
                                             final int maxEvaluations,
                                             final int maxIterations) {
        return create(model(model, jacobian),
                      new ArrayRealVector(observed, false),
                      new ArrayRealVector(start, false),
                      weight,
                      checker,
                      maxEvaluations,
                      maxIterations);
    }

    /**
     * Apply a dense weight matrix to the {@link LeastSquaresProblem}.
     *
     * @param problem the unweighted problem
     * @param weights the matrix of weights
     * @return a new {@link LeastSquaresProblem} with the weights applied. The original
     *         {@code problem} is not modified.
     */
    public static LeastSquaresProblem weightMatrix(final LeastSquaresProblem problem,
                                                   final RealMatrix weights) {
        final RealMatrix weightSquareRoot = squareRoot(weights);
        return new LeastSquaresAdapter(problem) {
            /** {@inheritDoc} */
            @Override
            public Evaluation evaluate(final RealVector point) {
                return new DenseWeightedEvaluation(super.evaluate(point), weightSquareRoot);
            }
        };
    }

    /**
     * Apply a diagonal weight matrix to the {@link LeastSquaresProblem}.
     *
     * @param problem the unweighted problem
     * @param weights the diagonal of the weight matrix
     * @return a new {@link LeastSquaresProblem} with the weights applied. The original
     *         {@code problem} is not modified.
     */
    public static LeastSquaresProblem weightDiagonal(final LeastSquaresProblem problem,
                                                     final RealVector weights) {
        // TODO more efficient implementation
        return weightMatrix(problem, new DiagonalMatrix(weights.toArray()));
    }

    /**
     * Count the evaluations of a particular problem. The {@code counter} will be
     * incremented every time {@link LeastSquaresProblem#evaluate(RealVector)} is called on
     * the <em>returned</em> problem.
     *
     * @param problem the problem to track.
     * @param counter the counter to increment.
     * @return a least squares problem that tracks evaluations
     */
    public static LeastSquaresProblem countEvaluations(final LeastSquaresProblem problem,
                                                       final Incrementor counter) {
        return new LeastSquaresAdapter(problem) {

            /** {@inheritDoc} */
            @Override
            public Evaluation evaluate(final RealVector point) {
                counter.incrementCount();
                return super.evaluate(point);
            }

            // Delegate the rest.
        };
    }

    /**
     * View a convergence checker specified for a {@link PointVectorValuePair} as one
     * specified for an {@link Evaluation}.
     *
     * @param checker the convergence checker to adapt.
     * @return a convergence checker that delegates to {@code checker}.
     */
    public static ConvergenceChecker<Evaluation> evaluationChecker(final ConvergenceChecker<PointVectorValuePair> checker) {
        return new ConvergenceChecker<Evaluation>() {
            /** {@inheritDoc} */
            public boolean converged(final int iteration,
                                     final Evaluation previous,
                                     final Evaluation current) {
                return checker.converged(
                        iteration,
                        new PointVectorValuePair(
                                previous.getPoint().toArray(),
                                previous.getResiduals().toArray(),
                                false),
                        new PointVectorValuePair(
                                current.getPoint().toArray(),
                                current.getResiduals().toArray(),
                                false)
                );
            }
        };
    }

    /**
     * Computes the square-root of the weight matrix.
     *
     * @param m Symmetric, positive-definite (weight) matrix.
     * @return the square-root of the weight matrix.
     */
    private static RealMatrix squareRoot(final RealMatrix m) {
        if (m instanceof DiagonalMatrix) {
            final int dim = m.getRowDimension();
            final RealMatrix sqrtM = new DiagonalMatrix(dim);
            for (int i = 0; i < dim; i++) {
                sqrtM.setEntry(i, i, FastMath.sqrt(m.getEntry(i, i)));
            }
            return sqrtM;
        } else {
            final EigenDecomposition dec = new EigenDecomposition(m);
            return dec.getSquareRoot();
        }
    }

    /**
     * Combine a {@link MultivariateVectorFunction} with a {@link
     * MultivariateMatrixFunction} to produce a {@link MultivariateJacobianFunction}.
     *
     * @param value    the vector value function
     * @param jacobian the Jacobian function
     * @return a function that computes both at the same time
     */
    public static MultivariateJacobianFunction model(final MultivariateVectorFunction value,
                                                     final MultivariateMatrixFunction jacobian) {
        return new LocalValueAndJacobianFunction(value, jacobian);
    }

    /**
     * Combine a {@link MultivariateVectorFunction} with a {@link
     * MultivariateMatrixFunction} to produce a {@link MultivariateJacobianFunction}.
     *
     * @param value    the vector value function
     * @param jacobian the Jacobian function
     * @return a function that computes both at the same time
     */
    private static class LocalValueAndJacobianFunction
        implements ValueAndJacobianFunction {
        /** Model. */
        private final MultivariateVectorFunction value;
        /** Model's Jacobian. */
        private final MultivariateMatrixFunction jacobian;

        /**
         * @param value Model function.
         * @param jacobian Model's Jacobian function.
         */
        LocalValueAndJacobianFunction(final MultivariateVectorFunction value,
                                      final MultivariateMatrixFunction jacobian) {
            this.value = value;
            this.jacobian = jacobian;
        }

        /** {@inheritDoc} */
        public Pair<RealVector, RealMatrix> value(final RealVector point) {
            //TODO get array from RealVector without copying?
            final double[] p = point.toArray();

            // Evaluate.
            return new Pair<RealVector, RealMatrix>(computeValue(p),
                                                    computeJacobian(p));
        }

        /** {@inheritDoc} */
        public RealVector computeValue(final double[] params) {
            return new ArrayRealVector(value.value(params), false);
        }

        /** {@inheritDoc} */
        public RealMatrix computeJacobian(final double[] params) {
            return new Array2DRowRealMatrix(jacobian.value(params), false);
        }
    }


    /**
     * A private, "field" immutable (not "real" immutable) implementation of {@link
     * LeastSquaresProblem}.
     * @since 3.3
     */
    private static class LocalLeastSquaresProblem
            extends AbstractOptimizationProblem<Evaluation>
            implements LeastSquaresProblem {

        /** Target values for the model function at optimum. */
        private final RealVector target;
        /** Model function. */
        private final MultivariateJacobianFunction model;
        /** Initial guess. */
        private final RealVector start;
        /** Whether to use lazy evaluation. */
        private final boolean lazyEvaluation;
        /** Model parameters validator. */
        private final ParameterValidator paramValidator;

        /**
         * Create a {@link LeastSquaresProblem} from the given data.
         *
         * @param model          the model function
         * @param target         the observed data
         * @param start          the initial guess
         * @param checker        the convergence checker
         * @param maxEvaluations the allowed evaluations
         * @param maxIterations  the allowed iterations
         * @param lazyEvaluation Whether the call to {@link Evaluation#evaluate(RealVector)}
         * will defer the evaluation until access to the value is requested.
         * @param paramValidator Model parameters validator.
         */
        LocalLeastSquaresProblem(final MultivariateJacobianFunction model,
                                 final RealVector target,
                                 final RealVector start,
                                 final ConvergenceChecker<Evaluation> checker,
                                 final int maxEvaluations,
                                 final int maxIterations,
                                 final boolean lazyEvaluation,
                                 final ParameterValidator paramValidator) {
            super(maxEvaluations, maxIterations, checker);
            this.target = target;
            this.model = model;
            this.start = start;
            this.lazyEvaluation = lazyEvaluation;
            this.paramValidator = paramValidator;

            if (lazyEvaluation &&
                !(model instanceof ValueAndJacobianFunction)) {
                // Lazy evaluation requires that value and Jacobian
                // can be computed separately.
                throw new MathIllegalStateException(LocalizedFormats.INVALID_IMPLEMENTATION,
                                                    model.getClass().getName());
            }
        }

        /** {@inheritDoc} */
        public int getObservationSize() {
            return target.getDimension();
        }

        /** {@inheritDoc} */
        public int getParameterSize() {
            return start.getDimension();
        }

        /** {@inheritDoc} */
        public RealVector getStart() {
            return start == null ? null : start.copy();
        }

        /** {@inheritDoc} */
        public Evaluation evaluate(final RealVector point) {
            // Copy so optimizer can change point without changing our instance.
            final RealVector p = paramValidator == null ?
                point.copy() :
                paramValidator.validate(point.copy());

            if (lazyEvaluation) {
                return new LazyUnweightedEvaluation((ValueAndJacobianFunction) model,
                                                    target,
                                                    p);
            } else {
                // Evaluate value and jacobian in one function call.
                final Pair<RealVector, RealMatrix> value = model.value(p);
                return new UnweightedEvaluation(value.getFirst(),
                                                value.getSecond(),
                                                target,
                                                p);
            }
        }

        /**
         * Container with the model evaluation at a particular point.
         */
        private static class UnweightedEvaluation extends AbstractEvaluation {
            /** Point of evaluation. */
            private final RealVector point;
            /** Derivative at point. */
            private final RealMatrix jacobian;
            /** Computed residuals. */
            private final RealVector residuals;

            /**
             * Create an {@link Evaluation} with no weights.
             *
             * @param values   the computed function values
             * @param jacobian the computed function Jacobian
             * @param target   the observed values
             * @param point    the abscissa
             */
            private UnweightedEvaluation(final RealVector values,
                                         final RealMatrix jacobian,
                                         final RealVector target,
                                         final RealVector point) {
                super(target.getDimension());
                this.jacobian = jacobian;
                this.point = point;
                this.residuals = target.subtract(values);
            }

            /** {@inheritDoc} */
            public RealMatrix getJacobian() {
                return jacobian;
            }

            /** {@inheritDoc} */
            public RealVector getPoint() {
                return point;
            }

            /** {@inheritDoc} */
            public RealVector getResiduals() {
                return residuals;
            }
        }

        /**
         * Container with the model <em>lazy</em> evaluation at a particular point.
         */
        private static class LazyUnweightedEvaluation extends AbstractEvaluation {
            /** Point of evaluation. */
            private final RealVector point;
            /** Model and Jacobian functions. */
            private final ValueAndJacobianFunction model;
            /** Target values for the model function at optimum. */
            private final RealVector target;

            /**
             * Create an {@link Evaluation} with no weights.
             *
             * @param model  the model function
             * @param target the observed values
             * @param point  the abscissa
             */
            private LazyUnweightedEvaluation(final ValueAndJacobianFunction model,
                                             final RealVector target,
                                             final RealVector point) {
                super(target.getDimension());
                // Safe to cast as long as we control usage of this class.
                this.model = model;
                this.point = point;
                this.target = target;
            }

            /** {@inheritDoc} */
            public RealMatrix getJacobian() {
                return model.computeJacobian(point.toArray());
            }

            /** {@inheritDoc} */
            public RealVector getPoint() {
                return point;
            }

            /** {@inheritDoc} */
            public RealVector getResiduals() {
                return target.subtract(model.computeValue(point.toArray()));
            }
        }
    }
}

