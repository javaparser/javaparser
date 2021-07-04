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
package org.apache.commons.math3.optim;

import org.apache.commons.math3.util.FastMath;
import org.apache.commons.math3.util.Pair;
import org.apache.commons.math3.exception.NotStrictlyPositiveException;

/**
 * Simple implementation of the {@link ConvergenceChecker} interface using
 * only point coordinates.
 *
 * Convergence is considered to have been reached if either the relative
 * difference between each point coordinate are smaller than a threshold
 * or if either the absolute difference between the point coordinates are
 * smaller than another threshold.
 * <br/>
 * The {@link #converged(int,Pair,Pair) converged} method will also return
 * {@code true} if the number of iterations has been set (see
 * {@link #SimplePointChecker(double,double,int) this constructor}).
 *
 * @param <PAIR> Type of the (point, value) pair.
 * The type of the "value" part of the pair (not used by this class).
 *
 * @since 3.0
 */
public class SimplePointChecker<PAIR extends Pair<double[], ? extends Object>>
    extends AbstractConvergenceChecker<PAIR> {
    /**
     * If {@link #maxIterationCount} is set to this value, the number of
     * iterations will never cause {@link #converged(int, Pair, Pair)}
     * to return {@code true}.
     */
    private static final int ITERATION_CHECK_DISABLED = -1;
    /**
     * Number of iterations after which the
     * {@link #converged(int, Pair, Pair)} method
     * will return true (unless the check is disabled).
     */
    private final int maxIterationCount;

    /**
     * Build an instance with specified thresholds.
     * In order to perform only relative checks, the absolute tolerance
     * must be set to a negative value. In order to perform only absolute
     * checks, the relative tolerance must be set to a negative value.
     *
     * @param relativeThreshold relative tolerance threshold
     * @param absoluteThreshold absolute tolerance threshold
     */
    public SimplePointChecker(final double relativeThreshold,
                              final double absoluteThreshold) {
        super(relativeThreshold, absoluteThreshold);
        maxIterationCount = ITERATION_CHECK_DISABLED;
    }

    /**
     * Builds an instance with specified thresholds.
     * In order to perform only relative checks, the absolute tolerance
     * must be set to a negative value. In order to perform only absolute
     * checks, the relative tolerance must be set to a negative value.
     *
     * @param relativeThreshold Relative tolerance threshold.
     * @param absoluteThreshold Absolute tolerance threshold.
     * @param maxIter Maximum iteration count.
     * @throws NotStrictlyPositiveException if {@code maxIter <= 0}.
     *
     * @since 3.1
     */
    public SimplePointChecker(final double relativeThreshold,
                              final double absoluteThreshold,
                              final int maxIter) {
        super(relativeThreshold, absoluteThreshold);

        if (maxIter <= 0) {
            throw new NotStrictlyPositiveException(maxIter);
        }
        maxIterationCount = maxIter;
    }

    /**
     * Check if the optimization algorithm has converged considering the
     * last two points.
     * This method may be called several times from the same algorithm
     * iteration with different points. This can be detected by checking the
     * iteration number at each call if needed. Each time this method is
     * called, the previous and current point correspond to points with the
     * same role at each iteration, so they can be compared. As an example,
     * simplex-based algorithms call this method for all points of the simplex,
     * not only for the best or worst ones.
     *
     * @param iteration Index of current iteration
     * @param previous Best point in the previous iteration.
     * @param current Best point in the current iteration.
     * @return {@code true} if the arguments satify the convergence criterion.
     */
    @Override
    public boolean converged(final int iteration,
                             final PAIR previous,
                             final PAIR current) {
        if (maxIterationCount != ITERATION_CHECK_DISABLED && iteration >= maxIterationCount) {
            return true;
        }

        final double[] p = previous.getKey();
        final double[] c = current.getKey();
        for (int i = 0; i < p.length; ++i) {
            final double pi = p[i];
            final double ci = c[i];
            final double difference = FastMath.abs(pi - ci);
            final double size = FastMath.max(FastMath.abs(pi), FastMath.abs(ci));
            if (difference > size * getRelativeThreshold() &&
                difference > getAbsoluteThreshold()) {
                return false;
            }
        }
        return true;
    }
}
