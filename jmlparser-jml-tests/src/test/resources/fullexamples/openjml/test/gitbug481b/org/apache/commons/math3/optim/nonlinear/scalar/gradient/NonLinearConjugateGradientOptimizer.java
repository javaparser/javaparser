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

package org.apache.commons.math3.optim.nonlinear.scalar.gradient;

import org.apache.commons.math3.analysis.solvers.UnivariateSolver;
import org.apache.commons.math3.exception.MathInternalError;
import org.apache.commons.math3.exception.TooManyEvaluationsException;
import org.apache.commons.math3.exception.MathUnsupportedOperationException;
import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.optim.OptimizationData;
import org.apache.commons.math3.optim.PointValuePair;
import org.apache.commons.math3.optim.ConvergenceChecker;
import org.apache.commons.math3.optim.nonlinear.scalar.GoalType;
import org.apache.commons.math3.optim.nonlinear.scalar.GradientMultivariateOptimizer;
import org.apache.commons.math3.optim.nonlinear.scalar.LineSearch;


/**
 * Non-linear conjugate gradient optimizer.
 * <br/>
 * This class supports both the Fletcher-Reeves and the Polak-Ribière
 * update formulas for the conjugate search directions.
 * It also supports optional preconditioning.
 * <br/>
 * Constraints are not supported: the call to
 * {@link #optimize(OptimizationData[]) optimize} will throw
 * {@link MathUnsupportedOperationException} if bounds are passed to it.
 *
 * @since 2.0
 */
public class NonLinearConjugateGradientOptimizer
    extends GradientMultivariateOptimizer {
    /** Update formula for the beta parameter. */
    private final Formula updateFormula;
    /** Preconditioner (may be null). */
    private final Preconditioner preconditioner;
    /** Line search algorithm. */
    private final LineSearch line;

    /**
     * Available choices of update formulas for the updating the parameter
     * that is used to compute the successive conjugate search directions.
     * For non-linear conjugate gradients, there are
     * two formulas:
     * <ul>
     *   <li>Fletcher-Reeves formula</li>
     *   <li>Polak-Ribière formula</li>
     * </ul>
     *
     * On the one hand, the Fletcher-Reeves formula is guaranteed to converge
     * if the start point is close enough of the optimum whether the
     * Polak-Ribière formula may not converge in rare cases. On the
     * other hand, the Polak-Ribière formula is often faster when it
     * does converge. Polak-Ribière is often used.
     *
     * @since 2.0
     */
    public enum Formula {
        /** Fletcher-Reeves formula. */
        FLETCHER_REEVES,
        /** Polak-Ribière formula. */
        POLAK_RIBIERE
    }

    /**
     * The initial step is a factor with respect to the search direction
     * (which itself is roughly related to the gradient of the function).
     * <br/>
     * It is used to find an interval that brackets the optimum in line
     * search.
     *
     * @since 3.1
     * @deprecated As of v3.3, this class is not used anymore.
     * This setting is replaced by the {@code initialBracketingRange}
     * argument to the new constructors.
     */
    @Deprecated
    public static class BracketingStep implements OptimizationData {
        /** Initial step. */
        private final double initialStep;

        /**
         * @param step Initial step for the bracket search.
         */
        public BracketingStep(double step) {
            initialStep = step;
        }

        /**
         * Gets the initial step.
         *
         * @return the initial step.
         */
        public double getBracketingStep() {
            return initialStep;
        }
    }

    /**
     * Constructor with default tolerances for the line search (1e-8) and
     * {@link IdentityPreconditioner preconditioner}.
     *
     * @param updateFormula formula to use for updating the &beta; parameter,
     * must be one of {@link Formula#FLETCHER_REEVES} or
     * {@link Formula#POLAK_RIBIERE}.
     * @param checker Convergence checker.
     */
    public NonLinearConjugateGradientOptimizer(final Formula updateFormula,
                                               ConvergenceChecker<PointValuePair> checker) {
        this(updateFormula,
             checker,
             1e-8,
             1e-8,
             1e-8,
             new IdentityPreconditioner());
    }

    /**
     * Constructor with default {@link IdentityPreconditioner preconditioner}.
     *
     * @param updateFormula formula to use for updating the &beta; parameter,
     * must be one of {@link Formula#FLETCHER_REEVES} or
     * {@link Formula#POLAK_RIBIERE}.
     * @param checker Convergence checker.
     * @param lineSearchSolver Solver to use during line search.
     * @deprecated as of 3.3. Please use
     * {@link #NonLinearConjugateGradientOptimizer(Formula,ConvergenceChecker,double,double,double)} instead.
     */
    @Deprecated
    public NonLinearConjugateGradientOptimizer(final Formula updateFormula,
                                               ConvergenceChecker<PointValuePair> checker,
                                               final UnivariateSolver lineSearchSolver) {
        this(updateFormula,
             checker,
             lineSearchSolver,
             new IdentityPreconditioner());
    }

    /**
     * Constructor with default {@link IdentityPreconditioner preconditioner}.
     *
     * @param updateFormula formula to use for updating the &beta; parameter,
     * must be one of {@link Formula#FLETCHER_REEVES} or
     * {@link Formula#POLAK_RIBIERE}.
     * @param checker Convergence checker.
     * @param relativeTolerance Relative threshold for line search.
     * @param absoluteTolerance Absolute threshold for line search.
     * @param initialBracketingRange Extent of the initial interval used to
     * find an interval that brackets the optimum in order to perform the
     * line search.
     *
     * @see LineSearch#LineSearch(MultivariateOptimizer,double,double,double)
     * @since 3.3
     */
    public NonLinearConjugateGradientOptimizer(final Formula updateFormula,
                                               ConvergenceChecker<PointValuePair> checker,
                                               double relativeTolerance,
                                               double absoluteTolerance,
                                               double initialBracketingRange) {
        this(updateFormula,
             checker,
             relativeTolerance,
             absoluteTolerance,
             initialBracketingRange,
             new IdentityPreconditioner());
    }

    /**
     * @param updateFormula formula to use for updating the &beta; parameter,
     * must be one of {@link Formula#FLETCHER_REEVES} or
     * {@link Formula#POLAK_RIBIERE}.
     * @param checker Convergence checker.
     * @param lineSearchSolver Solver to use during line search.
     * @param preconditioner Preconditioner.
     * @deprecated as of 3.3. Please use
     * {@link #NonLinearConjugateGradientOptimizer(Formula,ConvergenceChecker,double,double,double,Preconditioner)} instead.
     */
    @Deprecated
    public NonLinearConjugateGradientOptimizer(final Formula updateFormula,
                                               ConvergenceChecker<PointValuePair> checker,
                                               final UnivariateSolver lineSearchSolver,
                                               final Preconditioner preconditioner) {
        this(updateFormula,
             checker,
             lineSearchSolver.getRelativeAccuracy(),
             lineSearchSolver.getAbsoluteAccuracy(),
             lineSearchSolver.getAbsoluteAccuracy(),
             preconditioner);
    }

    /**
     * @param updateFormula formula to use for updating the &beta; parameter,
     * must be one of {@link Formula#FLETCHER_REEVES} or
     * {@link Formula#POLAK_RIBIERE}.
     * @param checker Convergence checker.
     * @param preconditioner Preconditioner.
     * @param relativeTolerance Relative threshold for line search.
     * @param absoluteTolerance Absolute threshold for line search.
     * @param initialBracketingRange Extent of the initial interval used to
     * find an interval that brackets the optimum in order to perform the
     * line search.
     *
     * @see LineSearch#LineSearch(MultivariateOptimizer,double,double,double)
     * @since 3.3
     */
    public NonLinearConjugateGradientOptimizer(final Formula updateFormula,
                                               ConvergenceChecker<PointValuePair> checker,
                                               double relativeTolerance,
                                               double absoluteTolerance,
                                               double initialBracketingRange,
                                               final Preconditioner preconditioner) {
        super(checker);

        this.updateFormula = updateFormula;
        this.preconditioner = preconditioner;
        line = new LineSearch(this,
                              relativeTolerance,
                              absoluteTolerance,
                              initialBracketingRange);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public PointValuePair optimize(OptimizationData... optData)
        throws TooManyEvaluationsException {
        // Set up base class and perform computation.
        return super.optimize(optData);
    }

    /** {@inheritDoc} */
    @Override
    protected PointValuePair doOptimize() {
        final ConvergenceChecker<PointValuePair> checker = getConvergenceChecker();
        final double[] point = getStartPoint();
        final GoalType goal = getGoalType();
        final int n = point.length;
        double[] r = computeObjectiveGradient(point);
        if (goal == GoalType.MINIMIZE) {
            for (int i = 0; i < n; i++) {
                r[i] = -r[i];
            }
        }

        // Initial search direction.
        double[] steepestDescent = preconditioner.precondition(point, r);
        double[] searchDirection = steepestDescent.clone();

        double delta = 0;
        for (int i = 0; i < n; ++i) {
            delta += r[i] * searchDirection[i];
        }

        PointValuePair current = null;
        while (true) {
            incrementIterationCount();

            final double objective = computeObjectiveValue(point);
            PointValuePair previous = current;
            current = new PointValuePair(point, objective);
            if (previous != null && checker.converged(getIterations(), previous, current)) {
                // We have found an optimum.
                return current;
            }

            final double step = line.search(point, searchDirection).getPoint();

            // Validate new point.
            for (int i = 0; i < point.length; ++i) {
                point[i] += step * searchDirection[i];
            }

            r = computeObjectiveGradient(point);
            if (goal == GoalType.MINIMIZE) {
                for (int i = 0; i < n; ++i) {
                    r[i] = -r[i];
                }
            }

            // Compute beta.
            final double deltaOld = delta;
            final double[] newSteepestDescent = preconditioner.precondition(point, r);
            delta = 0;
            for (int i = 0; i < n; ++i) {
                delta += r[i] * newSteepestDescent[i];
            }

            final double beta;
            switch (updateFormula) {
            case FLETCHER_REEVES:
                beta = delta / deltaOld;
                break;
            case POLAK_RIBIERE:
                double deltaMid = 0;
                for (int i = 0; i < r.length; ++i) {
                    deltaMid += r[i] * steepestDescent[i];
                }
                beta = (delta - deltaMid) / deltaOld;
                break;
            default:
                // Should never happen.
                throw new MathInternalError();
            }
            steepestDescent = newSteepestDescent;

            // Compute conjugate search direction.
            if (getIterations() % n == 0 ||
                beta < 0) {
                // Break conjugation: reset search direction.
                searchDirection = steepestDescent.clone();
            } else {
                // Compute new conjugate search direction.
                for (int i = 0; i < n; ++i) {
                    searchDirection[i] = steepestDescent[i] + beta * searchDirection[i];
                }
            }
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected void parseOptimizationData(OptimizationData... optData) {
        // Allow base class to register its own data.
        super.parseOptimizationData(optData);

        checkParameters();
    }

    /** Default identity preconditioner. */
    public static class IdentityPreconditioner implements Preconditioner {
        /** {@inheritDoc} */
        public double[] precondition(double[] variables, double[] r) {
            return r.clone();
        }
    }

    // Class is not used anymore (cf. MATH-1092). However, it might
    // be interesting to create a class similar to "LineSearch", but
    // that will take advantage that the model's gradient is available.
//     /**
//      * Internal class for line search.
//      * <p>
//      * The function represented by this class is the dot product of
//      * the objective function gradient and the search direction. Its
//      * value is zero when the gradient is orthogonal to the search
//      * direction, i.e. when the objective function value is a local
//      * extremum along the search direction.
//      * </p>
//      */
//     private class LineSearchFunction implements UnivariateFunction {
//         /** Current point. */
//         private final double[] currentPoint;
//         /** Search direction. */
//         private final double[] searchDirection;

//         /**
//          * @param point Current point.
//          * @param direction Search direction.
//          */
//         public LineSearchFunction(double[] point,
//                                   double[] direction) {
//             currentPoint = point.clone();
//             searchDirection = direction.clone();
//         }

//         /** {@inheritDoc} */
//         public double value(double x) {
//             // current point in the search direction
//             final double[] shiftedPoint = currentPoint.clone();
//             for (int i = 0; i < shiftedPoint.length; ++i) {
//                 shiftedPoint[i] += x * searchDirection[i];
//             }

//             // gradient of the objective function
//             final double[] gradient = computeObjectiveGradient(shiftedPoint);

//             // dot product with the search direction
//             double dotProduct = 0;
//             for (int i = 0; i < gradient.length; ++i) {
//                 dotProduct += gradient[i] * searchDirection[i];
//             }

//             return dotProduct;
//         }
//     }

    /**
     * @throws MathUnsupportedOperationException if bounds were passed to the
     * {@link #optimize(OptimizationData[]) optimize} method.
     */
    private void checkParameters() {
        if (getLowerBound() != null ||
            getUpperBound() != null) {
            throw new MathUnsupportedOperationException(LocalizedFormats.CONSTRAINT);
        }
    }
}
