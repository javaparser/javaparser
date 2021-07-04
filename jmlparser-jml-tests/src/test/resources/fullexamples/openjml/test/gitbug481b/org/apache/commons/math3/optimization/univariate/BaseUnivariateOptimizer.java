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

package org.apache.commons.math3.optimization.univariate;

import org.apache.commons.math3.analysis.UnivariateFunction;
import org.apache.commons.math3.optimization.BaseOptimizer;
import org.apache.commons.math3.optimization.GoalType;

/**
 * This interface is mainly intended to enforce the internal coherence of
 * Commons-Math. Users of the API are advised to base their code on
 * the following interfaces:
 * <ul>
 *  <li>{@link org.apache.commons.math3.optimization.univariate.UnivariateOptimizer}</li>
 * </ul>
 *
 * @param <FUNC> Type of the objective function to be optimized.
 *
 * @deprecated As of 3.1 (to be removed in 4.0).
 * @since 3.0
 */
@Deprecated
public interface BaseUnivariateOptimizer<FUNC extends UnivariateFunction>
    extends BaseOptimizer<UnivariatePointValuePair> {
    /**
     * Find an optimum in the given interval.
     *
     * An optimizer may require that the interval brackets a single optimum.
     *
     * @param f Function to optimize.
     * @param goalType Type of optimization goal: either
     * {@link GoalType#MAXIMIZE} or {@link GoalType#MINIMIZE}.
     * @param min Lower bound for the interval.
     * @param max Upper bound for the interval.
     * @param maxEval Maximum number of function evaluations.
     * @return a (point, value) pair where the function is optimum.
     * @throws org.apache.commons.math3.exception.TooManyEvaluationsException
     * if the maximum evaluation count is exceeded.
     * @throws org.apache.commons.math3.exception.ConvergenceException
     * if the optimizer detects a convergence problem.
     * @throws IllegalArgumentException if {@code min > max} or the endpoints
     * do not satisfy the requirements specified by the optimizer.
     */
    UnivariatePointValuePair optimize(int maxEval, FUNC f, GoalType goalType,
                                          double min, double max);

    /**
     * Find an optimum in the given interval, start at startValue.
     * An optimizer may require that the interval brackets a single optimum.
     *
     * @param f Function to optimize.
     * @param goalType Type of optimization goal: either
     * {@link GoalType#MAXIMIZE} or {@link GoalType#MINIMIZE}.
     * @param min Lower bound for the interval.
     * @param max Upper bound for the interval.
     * @param startValue Start value to use.
     * @param maxEval Maximum number of function evaluations.
     * @return a (point, value) pair where the function is optimum.
     * @throws org.apache.commons.math3.exception.TooManyEvaluationsException
     * if the maximum evaluation count is exceeded.
     * @throws org.apache.commons.math3.exception.ConvergenceException if the
     * optimizer detects a convergence problem.
     * @throws IllegalArgumentException if {@code min > max} or the endpoints
     * do not satisfy the requirements specified by the optimizer.
     * @throws org.apache.commons.math3.exception.NullArgumentException if any
     * argument is {@code null}.
     */
    UnivariatePointValuePair optimize(int maxEval, FUNC f, GoalType goalType,
                                          double min, double max,
                                          double startValue);
}
