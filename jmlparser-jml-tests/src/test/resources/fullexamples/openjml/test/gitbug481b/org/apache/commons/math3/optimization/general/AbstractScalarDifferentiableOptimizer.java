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

package org.apache.commons.math3.optimization.general;

import org.apache.commons.math3.analysis.DifferentiableMultivariateFunction;
import org.apache.commons.math3.analysis.MultivariateVectorFunction;
import org.apache.commons.math3.analysis.FunctionUtils;
import org.apache.commons.math3.analysis.differentiation.MultivariateDifferentiableFunction;
import org.apache.commons.math3.optimization.DifferentiableMultivariateOptimizer;
import org.apache.commons.math3.optimization.GoalType;
import org.apache.commons.math3.optimization.ConvergenceChecker;
import org.apache.commons.math3.optimization.PointValuePair;
import org.apache.commons.math3.optimization.direct.BaseAbstractMultivariateOptimizer;

/**
 * Base class for implementing optimizers for multivariate scalar
 * differentiable functions.
 * It contains boiler-plate code for dealing with gradient evaluation.
 *
 * @deprecated As of 3.1 (to be removed in 4.0).
 * @since 2.0
 */
@Deprecated
public abstract class AbstractScalarDifferentiableOptimizer
    extends BaseAbstractMultivariateOptimizer<DifferentiableMultivariateFunction>
    implements DifferentiableMultivariateOptimizer {
    /**
     * Objective function gradient.
     */
    private MultivariateVectorFunction gradient;

    /**
     * Simple constructor with default settings.
     * The convergence check is set to a
     * {@link org.apache.commons.math3.optimization.SimpleValueChecker
     * SimpleValueChecker}.
     * @deprecated See {@link org.apache.commons.math3.optimization.SimpleValueChecker#SimpleValueChecker()}
     */
    @Deprecated
    protected AbstractScalarDifferentiableOptimizer() {}

    /**
     * @param checker Convergence checker.
     */
    protected AbstractScalarDifferentiableOptimizer(ConvergenceChecker<PointValuePair> checker) {
        super(checker);
    }

    /**
     * Compute the gradient vector.
     *
     * @param evaluationPoint Point at which the gradient must be evaluated.
     * @return the gradient at the specified point.
     * @throws org.apache.commons.math3.exception.TooManyEvaluationsException
     * if the allowed number of evaluations is exceeded.
     */
    protected double[] computeObjectiveGradient(final double[] evaluationPoint) {
        return gradient.value(evaluationPoint);
    }

    /** {@inheritDoc} */
    @Override
    protected PointValuePair optimizeInternal(int maxEval,
                                              final DifferentiableMultivariateFunction f,
                                              final GoalType goalType,
                                              final double[] startPoint) {
        // Store optimization problem characteristics.
        gradient = f.gradient();

        return super.optimizeInternal(maxEval, f, goalType, startPoint);
    }

    /**
     * Optimize an objective function.
     *
     * @param f Objective function.
     * @param goalType Type of optimization goal: either
     * {@link GoalType#MAXIMIZE} or {@link GoalType#MINIMIZE}.
     * @param startPoint Start point for optimization.
     * @param maxEval Maximum number of function evaluations.
     * @return the point/value pair giving the optimal value for objective
     * function.
     * @throws org.apache.commons.math3.exception.DimensionMismatchException
     * if the start point dimension is wrong.
     * @throws org.apache.commons.math3.exception.TooManyEvaluationsException
     * if the maximal number of evaluations is exceeded.
     * @throws org.apache.commons.math3.exception.NullArgumentException if
     * any argument is {@code null}.
     */
    public PointValuePair optimize(final int maxEval,
                                   final MultivariateDifferentiableFunction f,
                                   final GoalType goalType,
                                   final double[] startPoint) {
        return optimizeInternal(maxEval,
                                FunctionUtils.toDifferentiableMultivariateFunction(f),
                                goalType,
                                startPoint);
    }
}
