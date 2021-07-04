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

import org.apache.commons.math3.analysis.MultivariateFunction;
import org.apache.commons.math3.optimization.BaseMultivariateOptimizer;
import org.apache.commons.math3.optimization.BaseMultivariateSimpleBoundsOptimizer;
import org.apache.commons.math3.optimization.GoalType;
import org.apache.commons.math3.optimization.InitialGuess;
import org.apache.commons.math3.optimization.SimpleBounds;
import org.apache.commons.math3.optimization.PointValuePair;
import org.apache.commons.math3.optimization.ConvergenceChecker;

/**
 * Base class for implementing optimizers for multivariate scalar functions,
 * subject to simple bounds: The valid range of the parameters is an interval.
 * The interval can possibly be infinite (in one or both directions).
 * This base class handles the boiler-plate methods associated to thresholds
 * settings, iterations and evaluations counting.
 *
 * @param <FUNC> Type of the objective function to be optimized.
 *
 * @deprecated As of 3.1 (to be removed in 4.0).
 * @since 3.0
 * @deprecated As of 3.1 since the {@link BaseAbstractMultivariateOptimizer
 * base class} contains similar functionality.
 */
@Deprecated
public abstract class BaseAbstractMultivariateSimpleBoundsOptimizer<FUNC extends MultivariateFunction>
    extends BaseAbstractMultivariateOptimizer<FUNC>
    implements BaseMultivariateOptimizer<FUNC>,
               BaseMultivariateSimpleBoundsOptimizer<FUNC> {
    /**
     * Simple constructor with default settings.
     * The convergence checker is set to a
     * {@link org.apache.commons.math3.optimization.SimpleValueChecker}.
     *
     * @see BaseAbstractMultivariateOptimizer#BaseAbstractMultivariateOptimizer()
     * @deprecated See {@link org.apache.commons.math3.optimization.SimpleValueChecker#SimpleValueChecker()}
     */
    @Deprecated
    protected BaseAbstractMultivariateSimpleBoundsOptimizer() {}

    /**
     * @param checker Convergence checker.
     */
    protected BaseAbstractMultivariateSimpleBoundsOptimizer(ConvergenceChecker<PointValuePair> checker) {
        super(checker);
    }

    /** {@inheritDoc} */
    @Override
    public PointValuePair optimize(int maxEval, FUNC f, GoalType goalType,
                                   double[] startPoint) {
        return super.optimizeInternal(maxEval, f, goalType,
                                      new InitialGuess(startPoint));
    }

    /** {@inheritDoc} */
    public PointValuePair optimize(int maxEval, FUNC f, GoalType goalType,
                                   double[] startPoint,
                                   double[] lower, double[] upper) {
        return super.optimizeInternal(maxEval, f, goalType,
                                      new InitialGuess(startPoint),
                                      new SimpleBounds(lower, upper));
    }
}
