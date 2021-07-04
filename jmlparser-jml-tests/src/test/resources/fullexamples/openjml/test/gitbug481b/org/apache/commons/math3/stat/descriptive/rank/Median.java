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
package org.apache.commons.math3.stat.descriptive.rank;

import java.io.Serializable;

import org.apache.commons.math3.exception.MathIllegalArgumentException;
import org.apache.commons.math3.exception.NullArgumentException;
import org.apache.commons.math3.stat.ranking.NaNStrategy;
import org.apache.commons.math3.util.KthSelector;


/**
 * Returns the median of the available values.  This is the same as the 50th percentile.
 * See {@link Percentile} for a description of the algorithm used.
 * <p>
 * <strong>Note that this implementation is not synchronized.</strong> If
 * multiple threads access an instance of this class concurrently, and at least
 * one of the threads invokes the <code>increment()</code> or
 * <code>clear()</code> method, it must be synchronized externally.</p>
 *
 */
public class Median extends Percentile implements Serializable {

    /** Serializable version identifier */
    private static final long serialVersionUID = -3961477041290915687L;

    /** Fixed quantile. */
    private static final double FIXED_QUANTILE_50 = 50.0;

    /**
     * Default constructor.
     */
    public Median() {
        // No try-catch or advertised exception - arg is valid
        super(FIXED_QUANTILE_50);
    }

    /**
     * Copy constructor, creates a new {@code Median} identical
     * to the {@code original}
     *
     * @param original the {@code Median} instance to copy
     * @throws NullArgumentException if original is null
     */
    public Median(Median original) throws NullArgumentException {
        super(original);
    }

    /**
     * Constructs a Median with the specific {@link EstimationType}, {@link NaNStrategy} and {@link PivotingStrategy}.
     *
     * @param estimationType one of the percentile {@link EstimationType  estimation types}
     * @param nanStrategy one of {@link NaNStrategy} to handle with NaNs
     * @param kthSelector {@link KthSelector} to use for pivoting during search
     * @throws MathIllegalArgumentException if p is not within (0,100]
     * @throws NullArgumentException if type or NaNStrategy passed is null
     */
    private Median(final EstimationType estimationType, final NaNStrategy nanStrategy,
                   final KthSelector kthSelector)
        throws MathIllegalArgumentException {
        super(FIXED_QUANTILE_50, estimationType, nanStrategy, kthSelector);
    }

    /** {@inheritDoc} */
    @Override
    public Median withEstimationType(final EstimationType newEstimationType) {
        return new Median(newEstimationType, getNaNStrategy(), getKthSelector());
    }

    /** {@inheritDoc} */
    @Override
    public Median withNaNStrategy(final NaNStrategy newNaNStrategy) {
        return new Median(getEstimationType(), newNaNStrategy, getKthSelector());
    }

    /** {@inheritDoc} */
    @Override
    public Median withKthSelector(final KthSelector newKthSelector) {
        return new Median(getEstimationType(), getNaNStrategy(), newKthSelector);
    }

}
