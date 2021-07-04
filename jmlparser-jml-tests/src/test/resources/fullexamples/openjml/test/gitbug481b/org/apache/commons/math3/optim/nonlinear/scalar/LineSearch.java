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

import org.apache.commons.math3.optim.univariate.UnivariateOptimizer;
import org.apache.commons.math3.optim.univariate.BrentOptimizer;
import org.apache.commons.math3.optim.univariate.BracketFinder;
import org.apache.commons.math3.optim.univariate.UnivariatePointValuePair;
import org.apache.commons.math3.optim.univariate.SimpleUnivariateValueChecker;
import org.apache.commons.math3.optim.univariate.SearchInterval;
import org.apache.commons.math3.optim.univariate.UnivariateObjectiveFunction;
import org.apache.commons.math3.analysis.UnivariateFunction;
import org.apache.commons.math3.optim.MaxEval;

/**
 * Class for finding the minimum of the objective function along a given
 * direction.
 *
 * @since 3.3
 */
public class LineSearch {
    /**
     * Value that will pass the precondition check for {@link BrentOptimizer}
     * but will not pass the convergence check, so that the custom checker
     * will always decide when to stop the line search.
     */
    private static final double REL_TOL_UNUSED = 1e-15;
    /**
     * Value that will pass the precondition check for {@link BrentOptimizer}
     * but will not pass the convergence check, so that the custom checker
     * will always decide when to stop the line search.
     */
    private static final double ABS_TOL_UNUSED = Double.MIN_VALUE;
    /**
     * Optimizer used for line search.
     */
    private final UnivariateOptimizer lineOptimizer;
    /**
     * Automatic bracketing.
     */
    private final BracketFinder bracket = new BracketFinder();
    /**
     * Extent of the initial interval used to find an interval that
     * brackets the optimum.
     */
    private final double initialBracketingRange;
    /**
     * Optimizer on behalf of which the line search must be performed.
     */
    private final MultivariateOptimizer mainOptimizer;

    /**
     * The {@code BrentOptimizer} default stopping criterion uses the
     * tolerances to check the domain (point) values, not the function
     * values.
     * The {@code relativeTolerance} and {@code absoluteTolerance}
     * arguments are thus passed to a {@link SimpleUnivariateValueChecker
     * custom checker} that will use the function values.
     *
     * @param optimizer Optimizer on behalf of which the line search
     * be performed.
     * Its {@link MultivariateOptimizer#computeObjectiveValue(double[])
     * computeObjectiveValue} method will be called by the
     * {@link #search(double[],double[]) search} method.
     * @param relativeTolerance Search will stop when the function relative
     * difference between successive iterations is below this value.
     * @param absoluteTolerance Search will stop when the function absolute
     * difference between successive iterations is below this value.
     * @param initialBracketingRange Extent of the initial interval used to
     * find an interval that brackets the optimum.
     * If the optimized function varies a lot in the vicinity of the optimum,
     * it may be necessary to provide a value lower than the distance between
     * successive local minima.
     */
    public LineSearch(MultivariateOptimizer optimizer,
                      double relativeTolerance,
                      double absoluteTolerance,
                      double initialBracketingRange) {
        mainOptimizer = optimizer;
        lineOptimizer = new BrentOptimizer(REL_TOL_UNUSED,
                                           ABS_TOL_UNUSED,
                                           new SimpleUnivariateValueChecker(relativeTolerance,
                                                                            absoluteTolerance));
        this.initialBracketingRange = initialBracketingRange;
    }

    /**
     * Finds the number {@code alpha} that optimizes
     * {@code f(startPoint + alpha * direction)}.
     *
     * @param startPoint Starting point.
     * @param direction Search direction.
     * @return the optimum.
     * @throws org.apache.commons.math3.exception.TooManyEvaluationsException
     * if the number of evaluations is exceeded.
     */
    public UnivariatePointValuePair search(final double[] startPoint,
                                           final double[] direction) {
        final int n = startPoint.length;
        final UnivariateFunction f = new UnivariateFunction() {
                /** {@inheritDoc} */
                public double value(double alpha) {
                    final double[] x = new double[n];
                    for (int i = 0; i < n; i++) {
                        x[i] = startPoint[i] + alpha * direction[i];
                    }
                    final double obj = mainOptimizer.computeObjectiveValue(x);
                    return obj;
                }
            };

        final GoalType goal = mainOptimizer.getGoalType();
        bracket.search(f, goal, 0, initialBracketingRange);
        // Passing "MAX_VALUE" as a dummy value because it is the enclosing
        // class that counts the number of evaluations (and will eventually
        // generate the exception).
        return lineOptimizer.optimize(new MaxEval(Integer.MAX_VALUE),
                                      new UnivariateObjectiveFunction(f),
                                      goal,
                                      new SearchInterval(bracket.getLo(),
                                                         bracket.getHi(),
                                                         bracket.getMid()));
    }
}
