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
package org.apache.commons.math3.analysis.integration;

import org.apache.commons.math3.analysis.UnivariateFunction;
import org.apache.commons.math3.analysis.solvers.UnivariateSolverUtils;
import org.apache.commons.math3.exception.MathIllegalArgumentException;
import org.apache.commons.math3.exception.MaxCountExceededException;
import org.apache.commons.math3.exception.NotStrictlyPositiveException;
import org.apache.commons.math3.exception.NullArgumentException;
import org.apache.commons.math3.exception.NumberIsTooSmallException;
import org.apache.commons.math3.exception.TooManyEvaluationsException;
import org.apache.commons.math3.util.IntegerSequence;
import org.apache.commons.math3.util.MathUtils;

/**
 * Provide a default implementation for several generic functions.
 *
 * @since 1.2
 */
public abstract class BaseAbstractUnivariateIntegrator implements UnivariateIntegrator {

    /** Default absolute accuracy. */
    public static final double DEFAULT_ABSOLUTE_ACCURACY = 1.0e-15;

    /** Default relative accuracy. */
    public static final double DEFAULT_RELATIVE_ACCURACY = 1.0e-6;

    /** Default minimal iteration count. */
    public static final int DEFAULT_MIN_ITERATIONS_COUNT = 3;

    /** Default maximal iteration count. */
    public static final int DEFAULT_MAX_ITERATIONS_COUNT = Integer.MAX_VALUE;

    /** The iteration count.
     * @deprecated as of 3.6, this field has been replaced with {@link #incrementCount()}
     */
    @Deprecated
    protected org.apache.commons.math3.util.Incrementor iterations;

    /** The iteration count. */
    private IntegerSequence.Incrementor count;

    /** Maximum absolute error. */
    private final double absoluteAccuracy;

    /** Maximum relative error. */
    private final double relativeAccuracy;

    /** minimum number of iterations */
    private final int minimalIterationCount;

    /** The functions evaluation count. */
    private IntegerSequence.Incrementor evaluations;

    /** Function to integrate. */
    private UnivariateFunction function;

    /** Lower bound for the interval. */
    private double min;

    /** Upper bound for the interval. */
    private double max;

    /**
     * Construct an integrator with given accuracies and iteration counts.
     * <p>
     * The meanings of the various parameters are:
     * <ul>
     *   <li>relative accuracy:
     *       this is used to stop iterations if the absolute accuracy can't be
     *       achieved due to large values or short mantissa length. If this
     *       should be the primary criterion for convergence rather then a
     *       safety measure, set the absolute accuracy to a ridiculously small value,
     *       like {@link org.apache.commons.math3.util.Precision#SAFE_MIN Precision.SAFE_MIN}.</li>
     *   <li>absolute accuracy:
     *       The default is usually chosen so that results in the interval
     *       -10..-0.1 and +0.1..+10 can be found with a reasonable accuracy. If the
     *       expected absolute value of your results is of much smaller magnitude, set
     *       this to a smaller value.</li>
     *   <li>minimum number of iterations:
     *       minimal iteration is needed to avoid false early convergence, e.g.
     *       the sample points happen to be zeroes of the function. Users can
     *       use the default value or choose one that they see as appropriate.</li>
     *   <li>maximum number of iterations:
     *       usually a high iteration count indicates convergence problems. However,
     *       the "reasonable value" varies widely for different algorithms. Users are
     *       advised to use the default value supplied by the algorithm.</li>
     * </ul>
     *
     * @param relativeAccuracy relative accuracy of the result
     * @param absoluteAccuracy absolute accuracy of the result
     * @param minimalIterationCount minimum number of iterations
     * @param maximalIterationCount maximum number of iterations
     * @exception NotStrictlyPositiveException if minimal number of iterations
     * is not strictly positive
     * @exception NumberIsTooSmallException if maximal number of iterations
     * is lesser than or equal to the minimal number of iterations
     */
    protected BaseAbstractUnivariateIntegrator(final double relativeAccuracy,
                                               final double absoluteAccuracy,
                                               final int minimalIterationCount,
                                               final int maximalIterationCount)
        throws NotStrictlyPositiveException, NumberIsTooSmallException {

        // accuracy settings
        this.relativeAccuracy      = relativeAccuracy;
        this.absoluteAccuracy      = absoluteAccuracy;

        // iterations count settings
        if (minimalIterationCount <= 0) {
            throw new NotStrictlyPositiveException(minimalIterationCount);
        }
        if (maximalIterationCount <= minimalIterationCount) {
            throw new NumberIsTooSmallException(maximalIterationCount, minimalIterationCount, false);
        }
        this.minimalIterationCount = minimalIterationCount;
        this.count                 = IntegerSequence.Incrementor.create().withMaximalCount(maximalIterationCount);

        @SuppressWarnings("deprecation")
        org.apache.commons.math3.util.Incrementor wrapped =
                        org.apache.commons.math3.util.Incrementor.wrap(count);
        this.iterations = wrapped;

        // prepare evaluations counter, but do not set it yet
        evaluations = IntegerSequence.Incrementor.create();

    }

    /**
     * Construct an integrator with given accuracies.
     * @param relativeAccuracy relative accuracy of the result
     * @param absoluteAccuracy absolute accuracy of the result
     */
    protected BaseAbstractUnivariateIntegrator(final double relativeAccuracy,
                                           final double absoluteAccuracy) {
        this(relativeAccuracy, absoluteAccuracy,
             DEFAULT_MIN_ITERATIONS_COUNT, DEFAULT_MAX_ITERATIONS_COUNT);
    }

    /**
     * Construct an integrator with given iteration counts.
     * @param minimalIterationCount minimum number of iterations
     * @param maximalIterationCount maximum number of iterations
     * @exception NotStrictlyPositiveException if minimal number of iterations
     * is not strictly positive
     * @exception NumberIsTooSmallException if maximal number of iterations
     * is lesser than or equal to the minimal number of iterations
     */
    protected BaseAbstractUnivariateIntegrator(final int minimalIterationCount,
                                           final int maximalIterationCount)
        throws NotStrictlyPositiveException, NumberIsTooSmallException {
        this(DEFAULT_RELATIVE_ACCURACY, DEFAULT_ABSOLUTE_ACCURACY,
             minimalIterationCount, maximalIterationCount);
    }

    /** {@inheritDoc} */
    public double getRelativeAccuracy() {
        return relativeAccuracy;
    }

    /** {@inheritDoc} */
    public double getAbsoluteAccuracy() {
        return absoluteAccuracy;
    }

    /** {@inheritDoc} */
    public int getMinimalIterationCount() {
        return minimalIterationCount;
    }

    /** {@inheritDoc} */
    public int getMaximalIterationCount() {
        return count.getMaximalCount();
    }

    /** {@inheritDoc} */
    public int getEvaluations() {
        return evaluations.getCount();
    }

    /** {@inheritDoc} */
    public int getIterations() {
        return count.getCount();
    }

    /** Increment the number of iterations.
     * @exception MaxCountExceededException if the number of iterations
     * exceeds the allowed maximum number
     */
    protected void incrementCount() throws MaxCountExceededException {
        count.increment();
    }

    /**
     * @return the lower bound.
     */
    protected double getMin() {
        return min;
    }
    /**
     * @return the upper bound.
     */
    protected double getMax() {
        return max;
    }

    /**
     * Compute the objective function value.
     *
     * @param point Point at which the objective function must be evaluated.
     * @return the objective function value at specified point.
     * @throws TooManyEvaluationsException if the maximal number of function
     * evaluations is exceeded.
     */
    protected double computeObjectiveValue(final double point)
        throws TooManyEvaluationsException {
        try {
            evaluations.increment();
        } catch (MaxCountExceededException e) {
            throw new TooManyEvaluationsException(e.getMax());
        }
        return function.value(point);
    }

    /**
     * Prepare for computation.
     * Subclasses must call this method if they override any of the
     * {@code solve} methods.
     *
     * @param maxEval Maximum number of evaluations.
     * @param f the integrand function
     * @param lower the min bound for the interval
     * @param upper the upper bound for the interval
     * @throws NullArgumentException if {@code f} is {@code null}.
     * @throws MathIllegalArgumentException if {@code min >= max}.
     */
    protected void setup(final int maxEval,
                         final UnivariateFunction f,
                         final double lower, final double upper)
        throws NullArgumentException, MathIllegalArgumentException {

        // Checks.
        MathUtils.checkNotNull(f);
        UnivariateSolverUtils.verifyInterval(lower, upper);

        // Reset.
        min = lower;
        max = upper;
        function = f;
        evaluations = evaluations.withMaximalCount(maxEval).withStart(0);
        count       = count.withStart(0);

    }

    /** {@inheritDoc} */
    public double integrate(final int maxEval, final UnivariateFunction f,
                            final double lower, final double upper)
        throws TooManyEvaluationsException, MaxCountExceededException,
               MathIllegalArgumentException, NullArgumentException {

        // Initialization.
        setup(maxEval, f, lower, upper);

        // Perform computation.
        return doIntegrate();

    }

    /**
     * Method for implementing actual integration algorithms in derived
     * classes.
     *
     * @return the root.
     * @throws TooManyEvaluationsException if the maximal number of evaluations
     * is exceeded.
     * @throws MaxCountExceededException if the maximum iteration count is exceeded
     * or the integrator detects convergence problems otherwise
     */
    protected abstract double doIntegrate()
        throws TooManyEvaluationsException, MaxCountExceededException;

}
