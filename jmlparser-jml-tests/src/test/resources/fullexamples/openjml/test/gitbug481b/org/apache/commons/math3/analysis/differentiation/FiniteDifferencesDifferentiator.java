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
package org.apache.commons.math3.analysis.differentiation;

import java.io.Serializable;

import org.apache.commons.math3.analysis.UnivariateFunction;
import org.apache.commons.math3.analysis.UnivariateMatrixFunction;
import org.apache.commons.math3.analysis.UnivariateVectorFunction;
import org.apache.commons.math3.exception.MathIllegalArgumentException;
import org.apache.commons.math3.exception.NotPositiveException;
import org.apache.commons.math3.exception.NumberIsTooLargeException;
import org.apache.commons.math3.exception.NumberIsTooSmallException;
import org.apache.commons.math3.util.FastMath;

/** Univariate functions differentiator using finite differences.
 * <p>
 * This class creates some wrapper objects around regular
 * {@link UnivariateFunction univariate functions} (or {@link
 * UnivariateVectorFunction univariate vector functions} or {@link
 * UnivariateMatrixFunction univariate matrix functions}). These
 * wrapper objects compute derivatives in addition to function
 * values.
 * </p>
 * <p>
 * The wrapper objects work by calling the underlying function on
 * a sampling grid around the current point and performing polynomial
 * interpolation. A finite differences scheme with n points is
 * theoretically able to compute derivatives up to order n-1, but
 * it is generally better to have a slight margin. The step size must
 * also be small enough in order for the polynomial approximation to
 * be good in the current point neighborhood, but it should not be too
 * small because numerical instability appears quickly (there are several
 * differences of close points). Choosing the number of points and
 * the step size is highly problem dependent.
 * </p>
 * <p>
 * As an example of good and bad settings, lets consider the quintic
 * polynomial function {@code f(x) = (x-1)*(x-0.5)*x*(x+0.5)*(x+1)}.
 * Since it is a polynomial, finite differences with at least 6 points
 * should theoretically recover the exact same polynomial and hence
 * compute accurate derivatives for any order. However, due to numerical
 * errors, we get the following results for a 7 points finite differences
 * for abscissae in the [-10, 10] range:
 * <ul>
 *   <li>step size = 0.25, second order derivative error about 9.97e-10</li>
 *   <li>step size = 0.25, fourth order derivative error about 5.43e-8</li>
 *   <li>step size = 1.0e-6, second order derivative error about 148</li>
 *   <li>step size = 1.0e-6, fourth order derivative error about 6.35e+14</li>
 * </ul>
 * <p>
 * This example shows that the small step size is really bad, even simply
 * for second order derivative!</p>
 *
 * @since 3.1
 */
public class FiniteDifferencesDifferentiator
    implements UnivariateFunctionDifferentiator, UnivariateVectorFunctionDifferentiator,
               UnivariateMatrixFunctionDifferentiator, Serializable {

    /** Serializable UID. */
    private static final long serialVersionUID = 20120917L;

    /** Number of points to use. */
    private final int nbPoints;

    /** Step size. */
    private final double stepSize;

    /** Half sample span. */
    private final double halfSampleSpan;

    /** Lower bound for independent variable. */
    private final double tMin;

    /** Upper bound for independent variable. */
    private final double tMax;

    /**
     * Build a differentiator with number of points and step size when independent variable is unbounded.
     * <p>
     * Beware that wrong settings for the finite differences differentiator
     * can lead to highly unstable and inaccurate results, especially for
     * high derivation orders. Using very small step sizes is often a
     * <em>bad</em> idea.
     * </p>
     * @param nbPoints number of points to use
     * @param stepSize step size (gap between each point)
     * @exception NotPositiveException if {@code stepsize <= 0} (note that
     * {@link NotPositiveException} extends {@link NumberIsTooSmallException})
     * @exception NumberIsTooSmallException {@code nbPoint <= 1}
     */
    public FiniteDifferencesDifferentiator(final int nbPoints, final double stepSize)
        throws NotPositiveException, NumberIsTooSmallException {
        this(nbPoints, stepSize, Double.NEGATIVE_INFINITY, Double.POSITIVE_INFINITY);
    }

    /**
     * Build a differentiator with number of points and step size when independent variable is bounded.
     * <p>
     * When the independent variable is bounded (tLower &lt; t &lt; tUpper), the sampling
     * points used for differentiation will be adapted to ensure the constraint holds
     * even near the boundaries. This means the sample will not be centered anymore in
     * these cases. At an extreme case, computing derivatives exactly at the lower bound
     * will lead the sample to be entirely on the right side of the derivation point.
     * </p>
     * <p>
     * Note that the boundaries are considered to be excluded for function evaluation.
     * </p>
     * <p>
     * Beware that wrong settings for the finite differences differentiator
     * can lead to highly unstable and inaccurate results, especially for
     * high derivation orders. Using very small step sizes is often a
     * <em>bad</em> idea.
     * </p>
     * @param nbPoints number of points to use
     * @param stepSize step size (gap between each point)
     * @param tLower lower bound for independent variable (may be {@code Double.NEGATIVE_INFINITY}
     * if there are no lower bounds)
     * @param tUpper upper bound for independent variable (may be {@code Double.POSITIVE_INFINITY}
     * if there are no upper bounds)
     * @exception NotPositiveException if {@code stepsize <= 0} (note that
     * {@link NotPositiveException} extends {@link NumberIsTooSmallException})
     * @exception NumberIsTooSmallException {@code nbPoint <= 1}
     * @exception NumberIsTooLargeException {@code stepSize * (nbPoints - 1) >= tUpper - tLower}
     */
    public FiniteDifferencesDifferentiator(final int nbPoints, final double stepSize,
                                           final double tLower, final double tUpper)
            throws NotPositiveException, NumberIsTooSmallException, NumberIsTooLargeException {

        if (nbPoints <= 1) {
            throw new NumberIsTooSmallException(stepSize, 1, false);
        }
        this.nbPoints = nbPoints;

        if (stepSize <= 0) {
            throw new NotPositiveException(stepSize);
        }
        this.stepSize = stepSize;

        halfSampleSpan = 0.5 * stepSize * (nbPoints - 1);
        if (2 * halfSampleSpan >= tUpper - tLower) {
            throw new NumberIsTooLargeException(2 * halfSampleSpan, tUpper - tLower, false);
        }
        final double safety = FastMath.ulp(halfSampleSpan);
        this.tMin = tLower + halfSampleSpan + safety;
        this.tMax = tUpper - halfSampleSpan - safety;

    }

    /**
     * Get the number of points to use.
     * @return number of points to use
     */
    public int getNbPoints() {
        return nbPoints;
    }

    /**
     * Get the step size.
     * @return step size
     */
    public double getStepSize() {
        return stepSize;
    }

    /**
     * Evaluate derivatives from a sample.
     * <p>
     * Evaluation is done using divided differences.
     * </p>
     * @param t evaluation abscissa value and derivatives
     * @param t0 first sample point abscissa
     * @param y function values sample {@code y[i] = f(t[i]) = f(t0 + i * stepSize)}
     * @return value and derivatives at {@code t}
     * @exception NumberIsTooLargeException if the requested derivation order
     * is larger or equal to the number of points
     */
    private DerivativeStructure evaluate(final DerivativeStructure t, final double t0,
                                         final double[] y)
        throws NumberIsTooLargeException {

        // create divided differences diagonal arrays
        final double[] top    = new double[nbPoints];
        final double[] bottom = new double[nbPoints];

        for (int i = 0; i < nbPoints; ++i) {

            // update the bottom diagonal of the divided differences array
            bottom[i] = y[i];
            for (int j = 1; j <= i; ++j) {
                bottom[i - j] = (bottom[i - j + 1] - bottom[i - j]) / (j * stepSize);
            }

            // update the top diagonal of the divided differences array
            top[i] = bottom[0];

        }

        // evaluate interpolation polynomial (represented by top diagonal) at t
        final int order            = t.getOrder();
        final int parameters       = t.getFreeParameters();
        final double[] derivatives = t.getAllDerivatives();
        final double dt0           = t.getValue() - t0;
        DerivativeStructure interpolation = new DerivativeStructure(parameters, order, 0.0);
        DerivativeStructure monomial = null;
        for (int i = 0; i < nbPoints; ++i) {
            if (i == 0) {
                // start with monomial(t) = 1
                monomial = new DerivativeStructure(parameters, order, 1.0);
            } else {
                // monomial(t) = (t - t0) * (t - t1) * ... * (t - t(i-1))
                derivatives[0] = dt0 - (i - 1) * stepSize;
                final DerivativeStructure deltaX = new DerivativeStructure(parameters, order, derivatives);
                monomial = monomial.multiply(deltaX);
            }
            interpolation = interpolation.add(monomial.multiply(top[i]));
        }

        return interpolation;

    }

    /** {@inheritDoc}
     * <p>The returned object cannot compute derivatives to arbitrary orders. The
     * value function will throw a {@link NumberIsTooLargeException} if the requested
     * derivation order is larger or equal to the number of points.
     * </p>
     */
    public UnivariateDifferentiableFunction differentiate(final UnivariateFunction function) {
        return new UnivariateDifferentiableFunction() {

            /** {@inheritDoc} */
            public double value(final double x) throws MathIllegalArgumentException {
                return function.value(x);
            }

            /** {@inheritDoc} */
            public DerivativeStructure value(final DerivativeStructure t)
                throws MathIllegalArgumentException {

                // check we can achieve the requested derivation order with the sample
                if (t.getOrder() >= nbPoints) {
                    throw new NumberIsTooLargeException(t.getOrder(), nbPoints, false);
                }

                // compute sample position, trying to be centered if possible
                final double t0 = FastMath.max(FastMath.min(t.getValue(), tMax), tMin) - halfSampleSpan;

                // compute sample points
                final double[] y = new double[nbPoints];
                for (int i = 0; i < nbPoints; ++i) {
                    y[i] = function.value(t0 + i * stepSize);
                }

                // evaluate derivatives
                return evaluate(t, t0, y);

            }

        };
    }

    /** {@inheritDoc}
     * <p>The returned object cannot compute derivatives to arbitrary orders. The
     * value function will throw a {@link NumberIsTooLargeException} if the requested
     * derivation order is larger or equal to the number of points.
     * </p>
     */
    public UnivariateDifferentiableVectorFunction differentiate(final UnivariateVectorFunction function) {
        return new UnivariateDifferentiableVectorFunction() {

            /** {@inheritDoc} */
            public double[]value(final double x) throws MathIllegalArgumentException {
                return function.value(x);
            }

            /** {@inheritDoc} */
            public DerivativeStructure[] value(final DerivativeStructure t)
                throws MathIllegalArgumentException {

                // check we can achieve the requested derivation order with the sample
                if (t.getOrder() >= nbPoints) {
                    throw new NumberIsTooLargeException(t.getOrder(), nbPoints, false);
                }

                // compute sample position, trying to be centered if possible
                final double t0 = FastMath.max(FastMath.min(t.getValue(), tMax), tMin) - halfSampleSpan;

                // compute sample points
                double[][] y = null;
                for (int i = 0; i < nbPoints; ++i) {
                    final double[] v = function.value(t0 + i * stepSize);
                    if (i == 0) {
                        y = new double[v.length][nbPoints];
                    }
                    for (int j = 0; j < v.length; ++j) {
                        y[j][i] = v[j];
                    }
                }

                // evaluate derivatives
                final DerivativeStructure[] value = new DerivativeStructure[y.length];
                for (int j = 0; j < value.length; ++j) {
                    value[j] = evaluate(t, t0, y[j]);
                }

                return value;

            }

        };
    }

    /** {@inheritDoc}
     * <p>The returned object cannot compute derivatives to arbitrary orders. The
     * value function will throw a {@link NumberIsTooLargeException} if the requested
     * derivation order is larger or equal to the number of points.
     * </p>
     */
    public UnivariateDifferentiableMatrixFunction differentiate(final UnivariateMatrixFunction function) {
        return new UnivariateDifferentiableMatrixFunction() {

            /** {@inheritDoc} */
            public double[][]  value(final double x) throws MathIllegalArgumentException {
                return function.value(x);
            }

            /** {@inheritDoc} */
            public DerivativeStructure[][]  value(final DerivativeStructure t)
                throws MathIllegalArgumentException {

                // check we can achieve the requested derivation order with the sample
                if (t.getOrder() >= nbPoints) {
                    throw new NumberIsTooLargeException(t.getOrder(), nbPoints, false);
                }

                // compute sample position, trying to be centered if possible
                final double t0 = FastMath.max(FastMath.min(t.getValue(), tMax), tMin) - halfSampleSpan;

                // compute sample points
                double[][][] y = null;
                for (int i = 0; i < nbPoints; ++i) {
                    final double[][] v = function.value(t0 + i * stepSize);
                    if (i == 0) {
                        y = new double[v.length][v[0].length][nbPoints];
                    }
                    for (int j = 0; j < v.length; ++j) {
                        for (int k = 0; k < v[j].length; ++k) {
                            y[j][k][i] = v[j][k];
                        }
                    }
                }

                // evaluate derivatives
                final DerivativeStructure[][] value = new DerivativeStructure[y.length][y[0].length];
                for (int j = 0; j < value.length; ++j) {
                    for (int k = 0; k < y[j].length; ++k) {
                        value[j][k] = evaluate(t, t0, y[j][k]);
                    }
                }

                return value;

            }

        };
    }

}
