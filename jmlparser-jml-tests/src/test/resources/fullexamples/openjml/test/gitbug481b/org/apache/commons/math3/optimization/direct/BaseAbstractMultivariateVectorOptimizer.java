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

package org.apache.commons.math3.optimization.direct;

import org.apache.commons.math3.util.Incrementor;
import org.apache.commons.math3.exception.MaxCountExceededException;
import org.apache.commons.math3.exception.TooManyEvaluationsException;
import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.NullArgumentException;
import org.apache.commons.math3.analysis.MultivariateVectorFunction;
import org.apache.commons.math3.optimization.OptimizationData;
import org.apache.commons.math3.optimization.InitialGuess;
import org.apache.commons.math3.optimization.Target;
import org.apache.commons.math3.optimization.Weight;
import org.apache.commons.math3.optimization.BaseMultivariateVectorOptimizer;
import org.apache.commons.math3.optimization.ConvergenceChecker;
import org.apache.commons.math3.optimization.PointVectorValuePair;
import org.apache.commons.math3.optimization.SimpleVectorValueChecker;
import org.apache.commons.math3.linear.RealMatrix;

/**
 * Base class for implementing optimizers for multivariate scalar functions.
 * This base class handles the boiler-plate methods associated to thresholds
 * settings, iterations and evaluations counting.
 *
 * @param <FUNC> the type of the objective function to be optimized
 *
 * @deprecated As of 3.1 (to be removed in 4.0).
 * @since 3.0
 */
@Deprecated
public abstract class BaseAbstractMultivariateVectorOptimizer<FUNC extends MultivariateVectorFunction>
    implements BaseMultivariateVectorOptimizer<FUNC> {
    /** Evaluations counter. */
    protected final Incrementor evaluations = new Incrementor();
    /** Convergence checker. */
    private ConvergenceChecker<PointVectorValuePair> checker;
    /** Target value for the objective functions at optimum. */
    private double[] target;
    /** Weight matrix. */
    private RealMatrix weightMatrix;
    /** Weight for the least squares cost computation.
     * @deprecated
     */
    @Deprecated
    private double[] weight;
    /** Initial guess. */
    private double[] start;
    /** Objective function. */
    private FUNC function;

    /**
     * Simple constructor with default settings.
     * The convergence check is set to a {@link SimpleVectorValueChecker}.
     * @deprecated See {@link SimpleVectorValueChecker#SimpleVectorValueChecker()}
     */
    @Deprecated
    protected BaseAbstractMultivariateVectorOptimizer() {
        this(new SimpleVectorValueChecker());
    }
    /**
     * @param checker Convergence checker.
     */
    protected BaseAbstractMultivariateVectorOptimizer(ConvergenceChecker<PointVectorValuePair> checker) {
        this.checker = checker;
    }

    /** {@inheritDoc} */
    public int getMaxEvaluations() {
        return evaluations.getMaximalCount();
    }

    /** {@inheritDoc} */
    public int getEvaluations() {
        return evaluations.getCount();
    }

    /** {@inheritDoc} */
    public ConvergenceChecker<PointVectorValuePair> getConvergenceChecker() {
        return checker;
    }

    /**
     * Compute the objective function value.
     *
     * @param point Point at which the objective function must be evaluated.
     * @return the objective function value at the specified point.
     * @throws TooManyEvaluationsException if the maximal number of evaluations is
     * exceeded.
     */
    protected double[] computeObjectiveValue(double[] point) {
        try {
            evaluations.incrementCount();
        } catch (MaxCountExceededException e) {
            throw new TooManyEvaluationsException(e.getMax());
        }
        return function.value(point);
    }

    /** {@inheritDoc}
     *
     * @deprecated As of 3.1. Please use
     * {@link #optimize(int,MultivariateVectorFunction,OptimizationData[])}
     * instead.
     */
    @Deprecated
    public PointVectorValuePair optimize(int maxEval, FUNC f, double[] t, double[] w,
                                         double[] startPoint) {
        return optimizeInternal(maxEval, f, t, w, startPoint);
    }

    /**
     * Optimize an objective function.
     *
     * @param maxEval Allowed number of evaluations of the objective function.
     * @param f Objective function.
     * @param optData Optimization data. The following data will be looked for:
     * <ul>
     *  <li>{@link Target}</li>
     *  <li>{@link Weight}</li>
     *  <li>{@link InitialGuess}</li>
     * </ul>
     * @return the point/value pair giving the optimal value of the objective
     * function.
     * @throws TooManyEvaluationsException if the maximal number of
     * evaluations is exceeded.
     * @throws DimensionMismatchException if the initial guess, target, and weight
     * arguments have inconsistent dimensions.
     *
     * @since 3.1
     */
    protected PointVectorValuePair optimize(int maxEval,
                                            FUNC f,
                                            OptimizationData... optData)
        throws TooManyEvaluationsException,
               DimensionMismatchException {
        return optimizeInternal(maxEval, f, optData);
    }

    /**
     * Optimize an objective function.
     * Optimization is considered to be a weighted least-squares minimization.
     * The cost function to be minimized is
     * <code>&sum;weight<sub>i</sub>(objective<sub>i</sub> - target<sub>i</sub>)<sup>2</sup></code>
     *
     * @param f Objective function.
     * @param t Target value for the objective functions at optimum.
     * @param w Weights for the least squares cost computation.
     * @param startPoint Start point for optimization.
     * @return the point/value pair giving the optimal value for objective
     * function.
     * @param maxEval Maximum number of function evaluations.
     * @throws org.apache.commons.math3.exception.DimensionMismatchException
     * if the start point dimension is wrong.
     * @throws org.apache.commons.math3.exception.TooManyEvaluationsException
     * if the maximal number of evaluations is exceeded.
     * @throws org.apache.commons.math3.exception.NullArgumentException if
     * any argument is {@code null}.
     * @deprecated As of 3.1. Please use
     * {@link #optimizeInternal(int,MultivariateVectorFunction,OptimizationData[])}
     * instead.
     */
    @Deprecated
    protected PointVectorValuePair optimizeInternal(final int maxEval, final FUNC f,
                                                    final double[] t, final double[] w,
                                                    final double[] startPoint) {
        // Checks.
        if (f == null) {
            throw new NullArgumentException();
        }
        if (t == null) {
            throw new NullArgumentException();
        }
        if (w == null) {
            throw new NullArgumentException();
        }
        if (startPoint == null) {
            throw new NullArgumentException();
        }
        if (t.length != w.length) {
            throw new DimensionMismatchException(t.length, w.length);
        }

        return optimizeInternal(maxEval, f,
                                new Target(t),
                                new Weight(w),
                                new InitialGuess(startPoint));
    }

    /**
     * Optimize an objective function.
     *
     * @param maxEval Allowed number of evaluations of the objective function.
     * @param f Objective function.
     * @param optData Optimization data. The following data will be looked for:
     * <ul>
     *  <li>{@link Target}</li>
     *  <li>{@link Weight}</li>
     *  <li>{@link InitialGuess}</li>
     * </ul>
     * @return the point/value pair giving the optimal value of the objective
     * function.
     * @throws TooManyEvaluationsException if the maximal number of
     * evaluations is exceeded.
     * @throws DimensionMismatchException if the initial guess, target, and weight
     * arguments have inconsistent dimensions.
     *
     * @since 3.1
     */
    protected PointVectorValuePair optimizeInternal(int maxEval,
                                                    FUNC f,
                                                    OptimizationData... optData)
        throws TooManyEvaluationsException,
               DimensionMismatchException {
        // Set internal state.
        evaluations.setMaximalCount(maxEval);
        evaluations.resetCount();
        function = f;
        // Retrieve other settings.
        parseOptimizationData(optData);
        // Check input consistency.
        checkParameters();
        // Allow subclasses to reset their own internal state.
        setUp();
        // Perform computation.
        return doOptimize();
    }

    /**
     * Gets the initial values of the optimized parameters.
     *
     * @return the initial guess.
     */
    public double[] getStartPoint() {
        return start.clone();
    }

    /**
     * Gets the weight matrix of the observations.
     *
     * @return the weight matrix.
     * @since 3.1
     */
    public RealMatrix getWeight() {
        return weightMatrix.copy();
    }
    /**
     * Gets the observed values to be matched by the objective vector
     * function.
     *
     * @return the target values.
     * @since 3.1
     */
    public double[] getTarget() {
        return target.clone();
    }

    /**
     * Gets the objective vector function.
     * Note that this access bypasses the evaluation counter.
     *
     * @return the objective vector function.
     * @since 3.1
     */
    protected FUNC getObjectiveFunction() {
        return function;
    }

    /**
     * Perform the bulk of the optimization algorithm.
     *
     * @return the point/value pair giving the optimal value for the
     * objective function.
     */
    protected abstract PointVectorValuePair doOptimize();

    /**
     * @return a reference to the {@link #target array}.
     * @deprecated As of 3.1.
     */
    @Deprecated
    protected double[] getTargetRef() {
        return target;
    }
    /**
     * @return a reference to the {@link #weight array}.
     * @deprecated As of 3.1.
     */
    @Deprecated
    protected double[] getWeightRef() {
        return weight;
    }

    /**
     * Method which a subclass <em>must</em> override whenever its internal
     * state depend on the {@link OptimizationData input} parsed by this base
     * class.
     * It will be called after the parsing step performed in the
     * {@link #optimize(int,MultivariateVectorFunction,OptimizationData[])
     * optimize} method and just before {@link #doOptimize()}.
     *
     * @since 3.1
     */
    protected void setUp() {
        // XXX Temporary code until the new internal data is used everywhere.
        final int dim = target.length;
        weight = new double[dim];
        for (int i = 0; i < dim; i++) {
            weight[i] = weightMatrix.getEntry(i, i);
        }
    }

    /**
     * Scans the list of (required and optional) optimization data that
     * characterize the problem.
     *
     * @param optData Optimization data. The following data will be looked for:
     * <ul>
     *  <li>{@link Target}</li>
     *  <li>{@link Weight}</li>
     *  <li>{@link InitialGuess}</li>
     * </ul>
     */
    private void parseOptimizationData(OptimizationData... optData) {
        // The existing values (as set by the previous call) are reused if
        // not provided in the argument list.
        for (OptimizationData data : optData) {
            if (data instanceof Target) {
                target = ((Target) data).getTarget();
                continue;
            }
            if (data instanceof Weight) {
                weightMatrix = ((Weight) data).getWeight();
                continue;
            }
            if (data instanceof InitialGuess) {
                start = ((InitialGuess) data).getInitialGuess();
                continue;
            }
        }
    }

    /**
     * Check parameters consistency.
     *
     * @throws DimensionMismatchException if {@link #target} and
     * {@link #weightMatrix} have inconsistent dimensions.
     */
    private void checkParameters() {
        if (target.length != weightMatrix.getColumnDimension()) {
            throw new DimensionMismatchException(target.length,
                                                 weightMatrix.getColumnDimension());
        }
    }
}
