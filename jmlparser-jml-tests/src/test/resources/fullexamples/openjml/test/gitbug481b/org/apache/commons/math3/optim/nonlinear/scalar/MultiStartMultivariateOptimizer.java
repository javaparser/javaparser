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

import java.util.Collections;
import java.util.List;
import java.util.ArrayList;
import java.util.Comparator;
import org.apache.commons.math3.exception.NotStrictlyPositiveException;
import org.apache.commons.math3.exception.NullArgumentException;
import org.apache.commons.math3.random.RandomVectorGenerator;
import org.apache.commons.math3.optim.BaseMultiStartMultivariateOptimizer;
import org.apache.commons.math3.optim.PointValuePair;

/**
 * Multi-start optimizer.
 *
 * This class wraps an optimizer in order to use it several times in
 * turn with different starting points (trying to avoid being trapped
 * in a local extremum when looking for a global one).
 *
 * @since 3.0
 */
public class MultiStartMultivariateOptimizer
    extends BaseMultiStartMultivariateOptimizer<PointValuePair> {
    /** Underlying optimizer. */
    private final MultivariateOptimizer optimizer;
    /** Found optima. */
    private final List<PointValuePair> optima = new ArrayList<PointValuePair>();

    /**
     * Create a multi-start optimizer from a single-start optimizer.
     *
     * @param optimizer Single-start optimizer to wrap.
     * @param starts Number of starts to perform.
     * If {@code starts == 1}, the result will be same as if {@code optimizer}
     * is called directly.
     * @param generator Random vector generator to use for restarts.
     * @throws NullArgumentException if {@code optimizer} or {@code generator}
     * is {@code null}.
     * @throws NotStrictlyPositiveException if {@code starts < 1}.
     */
    public MultiStartMultivariateOptimizer(final MultivariateOptimizer optimizer,
                                           final int starts,
                                           final RandomVectorGenerator generator)
        throws NullArgumentException,
        NotStrictlyPositiveException {
        super(optimizer, starts, generator);
        this.optimizer = optimizer;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public PointValuePair[] getOptima() {
        Collections.sort(optima, getPairComparator());
        return optima.toArray(new PointValuePair[0]);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected void store(PointValuePair optimum) {
        optima.add(optimum);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected void clear() {
        optima.clear();
    }

    /**
     * @return a comparator for sorting the optima.
     */
    private Comparator<PointValuePair> getPairComparator() {
        return new Comparator<PointValuePair>() {
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
                return (optimizer.getGoalType() == GoalType.MINIMIZE) ?
                    Double.compare(v1, v2) : Double.compare(v2, v1);
            }
        };
    }
}
