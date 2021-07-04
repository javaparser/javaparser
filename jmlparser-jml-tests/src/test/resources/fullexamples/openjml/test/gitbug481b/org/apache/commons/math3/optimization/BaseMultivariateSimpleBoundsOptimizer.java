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

package org.apache.commons.math3.optimization;

import org.apache.commons.math3.analysis.MultivariateFunction;

/**
 * This interface is mainly intended to enforce the internal coherence of
 * Commons-FastMath. Users of the API are advised to base their code on
 * the following interfaces:
 * <ul>
 *  <li>{@link org.apache.commons.math3.optimization.MultivariateOptimizer}</li>
 *  <li>{@link org.apache.commons.math3.optimization.MultivariateDifferentiableOptimizer}</li>
 * </ul>
 *
 * @param <FUNC> Type of the objective function to be optimized.
 *
 * @deprecated As of 3.1 (to be removed in 4.0).
 * @since 3.0
 */
@Deprecated
public interface BaseMultivariateSimpleBoundsOptimizer<FUNC extends MultivariateFunction>
    extends BaseMultivariateOptimizer<FUNC> {
    /**
     * Optimize an objective function.
     *
     * @param f Objective function.
     * @param goalType Type of optimization goal: either
     * {@link GoalType#MAXIMIZE} or {@link GoalType#MINIMIZE}.
     * @param startPoint Start point for optimization.
     * @param maxEval Maximum number of function evaluations.
     * @param lowerBound Lower bound for each of the parameters.
     * @param upperBound Upper bound for each of the parameters.
     * @return the point/value pair giving the optimal value for objective
     * function.
     * @throws org.apache.commons.math3.exception.DimensionMismatchException
     * if the array sizes are wrong.
     * @throws org.apache.commons.math3.exception.TooManyEvaluationsException
     * if the maximal number of evaluations is exceeded.
     * @throws org.apache.commons.math3.exception.NullArgumentException if
     * {@code f}, {@code goalType} or {@code startPoint} is {@code null}.
     * @throws org.apache.commons.math3.exception.NumberIsTooSmallException if any
     * of the initial values is less than its lower bound.
     * @throws org.apache.commons.math3.exception.NumberIsTooLargeException if any
     * of the initial values is greater than its upper bound.
     */
    PointValuePair optimize(int maxEval, FUNC f, GoalType goalType,
                                double[] startPoint,
                                double[] lowerBound, double[] upperBound);
}
