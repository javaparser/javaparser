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

import java.util.Arrays;
import java.util.Comparator;

import org.apache.commons.math3.analysis.MultivariateFunction;
import org.apache.commons.math3.exception.MathIllegalStateException;
import org.apache.commons.math3.exception.NotStrictlyPositiveException;
import org.apache.commons.math3.exception.NullArgumentException;
import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.random.RandomVectorGenerator;

/**
 * Base class for all implementations of a multi-start optimizer.
 *
 * This interface is mainly intended to enforce the internal coherence of
 * Commons-Math. Users of the API are advised to base their code on
 * {@link MultivariateMultiStartOptimizer} or on
 * {@link DifferentiableMultivariateMultiStartOptimizer}.
 *
 * @param <FUNC> Type of the objective function to be optimized.
 *
 * @deprecated As of 3.1 (to be removed in 4.0).
 * @since 3.0
 */
@Deprecated
public class BaseMultivariateMultiStartOptimizer<FUNC extends MultivariateFunction>
    implements BaseMultivariateOptimizer<FUNC> {
    /** Underlying classical optimizer. */
    private final BaseMultivariateOptimizer<FUNC> optimizer;
    /** Maximal number of evaluations allowed. */
    private int maxEvaluations;
    /** Number of evaluations already performed for all starts. */
    private int totalEvaluations;
    /** Number of starts to go. */
    private int starts;
    /** Random generator for multi-start. */
    private RandomVectorGenerator generator;
    /** Found optima. */
    private PointValuePair[] optima;

    /**
     * Create a multi-start optimizer from a single-start optimizer.
     *
     * @param optimizer Single-start optimizer to wrap.
     * @param starts Number of starts to perform. If {@code starts == 1},
     * the {@link #optimize(int,MultivariateFunction,GoalType,double[])
     * optimize} will return the same solution as {@code optimizer} would.
     * @param generator Random vector generator to use for restarts.
     * @throws NullArgumentException if {@code optimizer} or {@code generator}
     * is {@code null}.
     * @throws NotStrictlyPositiveException if {@code starts < 1}.
     */
    protected BaseMultivariateMultiStartOptimizer(final BaseMultivariateOptimizer<FUNC> optimizer,
                                                      final int starts,
                                                      final RandomVectorGenerator generator) {
        if (optimizer == null ||
            generator == null) {
            throw new NullArgumentException();
        }
        if (starts < 1) {
            throw new NotStrictlyPositiveException(starts);
        }

        this.optimizer = optimizer;
        this.starts = starts;
        this.generator = generator;
    }

    /**
     * Get all the optima found during the last call to {@link
     * #optimize(int,MultivariateFunction,GoalType,double[]) optimize}.
     * The optimizer stores all the optima found during a set of
     * restarts. The {@link #optimize(int,MultivariateFunction,GoalType,double[])
     * optimize} method returns the best point only. This method
     * returns all the points found at the end of each starts,
     * including the best one already returned by the {@link
     * #optimize(int,MultivariateFunction,GoalType,double[]) optimize} method.
     * <br/>
     * The returned array as one element for each start as specified
     * in the constructor. It is ordered with the results from the
     * runs that did converge first, sorted from best to worst
     * objective value (i.e in ascending order if minimizing and in
     * descending order if maximizing), followed by and null elements
     * corresponding to the runs that did not converge. This means all
     * elements will be null if the {@link #optimize(int,MultivariateFunction,GoalType,double[])
     * optimize} method did throw an exception.
     * This also means that if the first element is not {@code null}, it
     * is the best point found across all starts.
     *
     * @return an array containing the optima.
     * @throws MathIllegalStateException if {@link
     * #optimize(int,MultivariateFunction,GoalType,double[]) optimize}
     * has not been called.
     */
    public PointValuePair[] getOptima() {
        if (optima == null) {
            throw new MathIllegalStateException(LocalizedFormats.NO_OPTIMUM_COMPUTED_YET);
        }
        return optima.clone();
    }

    /** {@inheritDoc} */
    public int getMaxEvaluations() {
        return maxEvaluations;
    }

    /** {@inheritDoc} */
    public int getEvaluations() {
        return totalEvaluations;
    }

    /** {@inheritDoc} */
    public ConvergenceChecker<PointValuePair> getConvergenceChecker() {
        return optimizer.getConvergenceChecker();
    }

    /**
     * {@inheritDoc}
     */
    public PointValuePair optimize(int maxEval, final FUNC f,
                                       final GoalType goal,
                                       double[] startPoint) {
        maxEvaluations = maxEval;
        RuntimeException lastException = null;
        optima = new PointValuePair[starts];
        totalEvaluations = 0;

        // Multi-start loop.
        for (int i = 0; i < starts; ++i) {
            // CHECKSTYLE: stop IllegalCatch
            try {
                optima[i] = optimizer.optimize(maxEval - totalEvaluations, f, goal,
                                               i == 0 ? startPoint : generator.nextVector());
            } catch (RuntimeException mue) {
                lastException = mue;
                optima[i] = null;
            }
            // CHECKSTYLE: resume IllegalCatch

            totalEvaluations += optimizer.getEvaluations();
        }

        sortPairs(goal);

        if (optima[0] == null) {
            throw lastException; // cannot be null if starts >=1
        }

        // Return the found point given the best objective function value.
        return optima[0];
    }

    /**
     * Sort the optima from best to worst, followed by {@code null} elements.
     *
     * @param goal Goal type.
     */
    private void sortPairs(final GoalType goal) {
        Arrays.sort(optima, new Comparator<PointValuePair>() {
                /** {@inheritDoc} */
                public int compare(final PointValuePair o1,
                                   final PointValuePair o2) {
                    if (o1 == null) {
                        return (o2 == null) ? 0 : 1;
                    } else if (o2 == null) {
                        return -1;
                    }
                    final double v1 = o1.getValue();
                    final double v2 = o2.getValue();
                    return (goal == GoalType.MINIMIZE) ?
                        Double.compare(v1, v2) : Double.compare(v2, v1);
                }
            });
    }
}
