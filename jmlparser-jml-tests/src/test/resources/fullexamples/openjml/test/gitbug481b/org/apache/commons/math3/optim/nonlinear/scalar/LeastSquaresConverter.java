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

package org.apache.commons.math3.optim.nonlinear.scalar;

import org.apache.commons.math3.analysis.MultivariateFunction;
import org.apache.commons.math3.analysis.MultivariateVectorFunction;
import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.linear.RealMatrix;

/**
 * This class converts
 * {@link MultivariateVectorFunction vectorial objective functions} to
 * {@link MultivariateFunction scalar objective functions}
 * when the goal is to minimize them.
 * <br/>
 * This class is mostly used when the vectorial objective function represents
 * a theoretical result computed from a point set applied to a model and
 * the models point must be adjusted to fit the theoretical result to some
 * reference observations. The observations may be obtained for example from
 * physical measurements whether the model is built from theoretical
 * considerations.
 * <br/>
 * This class computes a possibly weighted squared sum of the residuals, which is
 * a scalar value. The residuals are the difference between the theoretical model
 * (i.e. the output of the vectorial objective function) and the observations. The
 * class implements the {@link MultivariateFunction} interface and can therefore be
 * minimized by any optimizer supporting scalar objectives functions.This is one way
 * to perform a least square estimation. There are other ways to do this without using
 * this converter, as some optimization algorithms directly support vectorial objective
 * functions.
 * <br/>
 * This class support combination of residuals with or without weights and correlations.
  *
 * @see MultivariateFunction
 * @see MultivariateVectorFunction
 * @since 2.0
 */

public class LeastSquaresConverter implements MultivariateFunction {
    /** Underlying vectorial function. */
    private final MultivariateVectorFunction function;
    /** Observations to be compared to objective function to compute residuals. */
    private final double[] observations;
    /** Optional weights for the residuals. */
    private final double[] weights;
    /** Optional scaling matrix (weight and correlations) for the residuals. */
    private final RealMatrix scale;

    /**
     * Builds a simple converter for uncorrelated residuals with identical
     * weights.
     *
     * @param function vectorial residuals function to wrap
     * @param observations observations to be compared to objective function to compute residuals
     */
    public LeastSquaresConverter(final MultivariateVectorFunction function,
                                 final double[] observations) {
        this.function     = function;
        this.observations = observations.clone();
        this.weights      = null;
        this.scale        = null;
    }

    /**
     * Builds a simple converter for uncorrelated residuals with the
     * specified weights.
     * <p>
     * The scalar objective function value is computed as:
     * <pre>
     * objective = &sum;weight<sub>i</sub>(observation<sub>i</sub>-objective<sub>i</sub>)<sup>2</sup>
     * </pre>
     * </p>
     * <p>
     * Weights can be used for example to combine residuals with different standard
     * deviations. As an example, consider a residuals array in which even elements
     * are angular measurements in degrees with a 0.01&deg; standard deviation and
     * odd elements are distance measurements in meters with a 15m standard deviation.
     * In this case, the weights array should be initialized with value
     * 1.0/(0.01<sup>2</sup>) in the even elements and 1.0/(15.0<sup>2</sup>) in the
     * odd elements (i.e. reciprocals of variances).
     * </p>
     * <p>
     * The array computed by the objective function, the observations array and the
     * weights array must have consistent sizes or a {@link DimensionMismatchException}
     * will be triggered while computing the scalar objective.
     * </p>
     *
     * @param function vectorial residuals function to wrap
     * @param observations observations to be compared to objective function to compute residuals
     * @param weights weights to apply to the residuals
     * @throws DimensionMismatchException if the observations vector and the weights
     * vector dimensions do not match (objective function dimension is checked only when
     * the {@link #value(double[])} method is called)
     */
    public LeastSquaresConverter(final MultivariateVectorFunction function,
                                 final double[] observations,
                                 final double[] weights) {
        if (observations.length != weights.length) {
            throw new DimensionMismatchException(observations.length, weights.length);
        }
        this.function     = function;
        this.observations = observations.clone();
        this.weights      = weights.clone();
        this.scale        = null;
    }

    /**
     * Builds a simple converter for correlated residuals with the
     * specified weights.
     * <p>
     * The scalar objective function value is computed as:
     * <pre>
     * objective = y<sup>T</sup>y with y = scale&times;(observation-objective)
     * </pre>
     * </p>
     * <p>
     * The array computed by the objective function, the observations array and the
     * the scaling matrix must have consistent sizes or a {@link DimensionMismatchException}
     * will be triggered while computing the scalar objective.
     * </p>
     *
     * @param function vectorial residuals function to wrap
     * @param observations observations to be compared to objective function to compute residuals
     * @param scale scaling matrix
     * @throws DimensionMismatchException if the observations vector and the scale
     * matrix dimensions do not match (objective function dimension is checked only when
     * the {@link #value(double[])} method is called)
     */
    public LeastSquaresConverter(final MultivariateVectorFunction function,
                                 final double[] observations,
                                 final RealMatrix scale) {
        if (observations.length != scale.getColumnDimension()) {
            throw new DimensionMismatchException(observations.length, scale.getColumnDimension());
        }
        this.function     = function;
        this.observations = observations.clone();
        this.weights      = null;
        this.scale        = scale.copy();
    }

    /** {@inheritDoc} */
    public double value(final double[] point) {
        // compute residuals
        final double[] residuals = function.value(point);
        if (residuals.length != observations.length) {
            throw new DimensionMismatchException(residuals.length, observations.length);
        }
        for (int i = 0; i < residuals.length; ++i) {
            residuals[i] -= observations[i];
        }

        // compute sum of squares
        double sumSquares = 0;
        if (weights != null) {
            for (int i = 0; i < residuals.length; ++i) {
                final double ri = residuals[i];
                sumSquares +=  weights[i] * ri * ri;
            }
        } else if (scale != null) {
            for (final double yi : scale.operate(residuals)) {
                sumSquares += yi * yi;
            }
        } else {
            for (final double ri : residuals) {
                sumSquares += ri * ri;
            }
        }

        return sumSquares;
    }
}
