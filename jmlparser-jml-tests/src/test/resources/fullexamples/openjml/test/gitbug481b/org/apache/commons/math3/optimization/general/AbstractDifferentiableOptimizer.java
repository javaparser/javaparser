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

import org.apache.commons.math3.analysis.MultivariateVectorFunction;
import org.apache.commons.math3.analysis.differentiation.GradientFunction;
import org.apache.commons.math3.analysis.differentiation.MultivariateDifferentiableFunction;
import org.apache.commons.math3.optimization.ConvergenceChecker;
import org.apache.commons.math3.optimization.GoalType;
import org.apache.commons.math3.optimization.OptimizationData;
import org.apache.commons.math3.optimization.InitialGuess;
import org.apache.commons.math3.optimization.PointValuePair;
import org.apache.commons.math3.optimization.direct.BaseAbstractMultivariateOptimizer;

/**
 * Base class for implementing optimizers for multivariate scalar
 * differentiable functions.
 * It contains boiler-plate code for dealing with gradient evaluation.
 *
 * @deprecated As of 3.1 (to be removed in 4.0).
 * @since 3.1
 */
@Deprecated
public abstract class AbstractDifferentiableOptimizer
    extends BaseAbstractMultivariateOptimizer<MultivariateDifferentiableFunction> {
    /**
     * Objective function gradient.
     */
    private MultivariateVectorFunction gradient;

    /**
     * @param checker Convergence checker.
     */
    protected AbstractDifferentiableOptimizer(ConvergenceChecker<PointValuePair> checker) {
        super(checker);
    }

    /**
     * Compute the gradient vector.
     *
     * @param evaluationPoint Point at which the gradient must be evaluated.
     * @return the gradient at the specified point.
     */
    protected double[] computeObjectiveGradient(final double[] evaluationPoint) {
        return gradient.value(evaluationPoint);
    }

    /**
     * {@inheritDoc}
     *
     * @deprecated In 3.1. Please use
     * {@link #optimizeInternal(int,MultivariateDifferentiableFunction,GoalType,OptimizationData[])}
     * instead.
     */
    @Override@Deprecated
    protected PointValuePair optimizeInternal(final int maxEval,
                                              final MultivariateDifferentiableFunction f,
                                              final GoalType goalType,
                                              final double[] startPoint) {
        return optimizeInternal(maxEval, f, goalType, new InitialGuess(startPoint));
    }

    /** {@inheritDoc} */
    @Override
    protected PointValuePair optimizeInternal(final int maxEval,
                                              final MultivariateDifferentiableFunction f,
                                              final GoalType goalType,
                                              final OptimizationData... optData) {
        // Store optimization problem characteristics.
        gradient = new GradientFunction(f);

        // Perform optimization.
        return super.optimizeInternal(maxEval, f, goalType, optData);
    }
}
