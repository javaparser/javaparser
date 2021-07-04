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
package org.apache.commons.math3.optim.nonlinear.vector;

import java.util.Collections;
import java.util.List;
import java.util.ArrayList;
import java.util.Comparator;
import org.apache.commons.math3.exception.NotStrictlyPositiveException;
import org.apache.commons.math3.exception.NullArgumentException;
import org.apache.commons.math3.linear.RealMatrix;
import org.apache.commons.math3.linear.RealVector;
import org.apache.commons.math3.linear.ArrayRealVector;
import org.apache.commons.math3.random.RandomVectorGenerator;
import org.apache.commons.math3.optim.BaseMultiStartMultivariateOptimizer;
import org.apache.commons.math3.optim.PointVectorValuePair;

/**
 * Multi-start optimizer for a (vector) model function.
 *
 * This class wraps an optimizer in order to use it several times in
 * turn with different starting points (trying to avoid being trapped
 * in a local extremum when looking for a global one).
 *
 * @since 3.0
 */
@Deprecated
public class MultiStartMultivariateVectorOptimizer
    extends BaseMultiStartMultivariateOptimizer<PointVectorValuePair> {
    /** Underlying optimizer. */
    private final MultivariateVectorOptimizer optimizer;
    /** Found optima. */
    private final List<PointVectorValuePair> optima = new ArrayList<PointVectorValuePair>();

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
    public MultiStartMultivariateVectorOptimizer(final MultivariateVectorOptimizer optimizer,
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
    public PointVectorValuePair[] getOptima() {
        Collections.sort(optima, getPairComparator());
        return optima.toArray(new PointVectorValuePair[0]);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected void store(PointVectorValuePair optimum) {
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
    private Comparator<PointVectorValuePair> getPairComparator() {
        return new Comparator<PointVectorValuePair>() {
            /** Observed value to be matched. */
            private final RealVector target = new ArrayRealVector(optimizer.getTarget(), false);
            /** Observations weights. */
            private final RealMatrix weight = optimizer.getWeight();

            /** {@inheritDoc} */
            public int compare(final PointVectorValuePair o1,
                               final PointVectorValuePair o2) {
                if (o1 == null) {
                    return (o2 == null) ? 0 : 1;
                } else if (o2 == null) {
                    return -1;
                }
                return Double.compare(weightedResidual(o1),
                                      weightedResidual(o2));
            }

            private double weightedResidual(final PointVectorValuePair pv) {
                final RealVector v = new ArrayRealVector(pv.getValueRef(), false);
                final RealVector r = target.subtract(v);
                return r.dotProduct(weight.operate(r));
            }
        };
    }
}
