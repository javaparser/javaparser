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
import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.NumberIsTooSmallException;
import org.apache.commons.math3.util.FastMath;
import org.apache.commons.math3.util.MathUtils;

/**
 * <p>Adapter extending bounded {@link MultivariateFunction} to an unbouded
 * domain using a penalty function.</p>
 *
 * <p>
 * This adapter can be used to wrap functions subject to simple bounds on
 * parameters so they can be used by optimizers that do <em>not</em> directly
 * support simple bounds.
 * </p>
 * <p>
 * The principle is that the user function that will be wrapped will see its
 * parameters bounded as required, i.e when its {@code value} method is called
 * with argument array {@code point}, the elements array will fulfill requirement
 * {@code lower[i] <= point[i] <= upper[i]} for all i. Some of the components
 * may be unbounded or bounded only on one side if the corresponding bound is
 * set to an infinite value. The optimizer will not manage the user function by
 * itself, but it will handle this adapter and it is this adapter that will take
 * care the bounds are fulfilled. The adapter {@link #value(double[])} method will
 * be called by the optimizer with unbound parameters, and the adapter will check
 * if the parameters is within range or not. If it is in range, then the underlying
 * user function will be called, and if it is not the value of a penalty function
 * will be returned instead.
 * </p>
 * <p>
 * This adapter is only a poor-man's solution to simple bounds optimization
 * constraints that can be used with simple optimizers like
 * {@link org.apache.commons.math3.optim.nonlinear.scalar.noderiv.SimplexOptimizer
 * SimplexOptimizer}.
 * A better solution is to use an optimizer that directly supports simple bounds like
 * {@link org.apache.commons.math3.optim.nonlinear.scalar.noderiv.CMAESOptimizer
 * CMAESOptimizer} or
 * {@link org.apache.commons.math3.optim.nonlinear.scalar.noderiv.BOBYQAOptimizer
 * BOBYQAOptimizer}.
 * One caveat of this poor-man's solution is that if start point or start simplex
 * is completely outside of the allowed range, only the penalty function is used,
 * and the optimizer may converge without ever entering the range.
 * </p>
 *
 * @see MultivariateFunctionMappingAdapter
 *
 * @since 3.0
 */
public class MultivariateFunctionPenaltyAdapter
    implements MultivariateFunction {
    /** Underlying bounded function. */
    private final MultivariateFunction bounded;
    /** Lower bounds. */
    private final double[] lower;
    /** Upper bounds. */
    private final double[] upper;
    /** Penalty offset. */
    private final double offset;
    /** Penalty scales. */
    private final double[] scale;

    /**
     * Simple constructor.
     * <p>
     * When the optimizer provided points are out of range, the value of the
     * penalty function will be used instead of the value of the underlying
     * function. In order for this penalty to be effective in rejecting this
     * point during the optimization process, the penalty function value should
     * be defined with care. This value is computed as:
     * <pre>
     *   penalty(point) = offset + &sum;<sub>i</sub>[scale[i] * &radic;|point[i]-boundary[i]|]
     * </pre>
     * where indices i correspond to all the components that violates their boundaries.
     * </p>
     * <p>
     * So when attempting a function minimization, offset should be larger than
     * the maximum expected value of the underlying function and scale components
     * should all be positive. When attempting a function maximization, offset
     * should be lesser than the minimum expected value of the underlying function
     * and scale components should all be negative.
     * minimization, and lesser than the minimum expected value of the underlying
     * function when attempting maximization.
     * </p>
     * <p>
     * These choices for the penalty function have two properties. First, all out
     * of range points will return a function value that is worse than the value
     * returned by any in range point. Second, the penalty is worse for large
     * boundaries violation than for small violations, so the optimizer has an hint
     * about the direction in which it should search for acceptable points.
     * </p>
     * @param bounded bounded function
     * @param lower lower bounds for each element of the input parameters array
     * (some elements may be set to {@code Double.NEGATIVE_INFINITY} for
     * unbounded values)
     * @param upper upper bounds for each element of the input parameters array
     * (some elements may be set to {@code Double.POSITIVE_INFINITY} for
     * unbounded values)
     * @param offset base offset of the penalty function
     * @param scale scale of the penalty function
     * @exception DimensionMismatchException if lower bounds, upper bounds and
     * scales are not consistent, either according to dimension or to bounadary
     * values
     */
    public MultivariateFunctionPenaltyAdapter(final MultivariateFunction bounded,
                                              final double[] lower, final double[] upper,
                                              final double offset, final double[] scale) {

        // safety checks
        MathUtils.checkNotNull(lower);
        MathUtils.checkNotNull(upper);
        MathUtils.checkNotNull(scale);
        if (lower.length != upper.length) {
            throw new DimensionMismatchException(lower.length, upper.length);
        }
        if (lower.length != scale.length) {
            throw new DimensionMismatchException(lower.length, scale.length);
        }
        for (int i = 0; i < lower.length; ++i) {
            // note the following test is written in such a way it also fails for NaN
            if (!(upper[i] >= lower[i])) {
                throw new NumberIsTooSmallException(upper[i], lower[i], true);
            }
        }

        this.bounded = bounded;
        this.lower   = lower.clone();
        this.upper   = upper.clone();
        this.offset  = offset;
        this.scale   = scale.clone();
    }

    /**
     * Computes the underlying function value from an unbounded point.
     * <p>
     * This method simply returns the value of the underlying function
     * if the unbounded point already fulfills the bounds, and compute
     * a replacement value using the offset and scale if bounds are
     * violated, without calling the function at all.
     * </p>
     * @param point unbounded point
     * @return either underlying function value or penalty function value
     */
    public double value(double[] point) {

        for (int i = 0; i < scale.length; ++i) {
            if ((point[i] < lower[i]) || (point[i] > upper[i])) {
                // bound violation starting at this component
                double sum = 0;
                for (int j = i; j < scale.length; ++j) {
                    final double overshoot;
                    if (point[j] < lower[j]) {
                        overshoot = scale[j] * (lower[j] - point[j]);
                    } else if (point[j] > upper[j]) {
                        overshoot = scale[j] * (point[j] - upper[j]);
                    } else {
                        overshoot = 0;
                    }
                    sum += FastMath.sqrt(overshoot);
                }
                return offset + sum;
            }
        }

        // all boundaries are fulfilled, we are in the expected
        // domain of the underlying function
        return bounded.value(point);
    }
}
