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
package org.apache.commons.math3.optim.univariate;

import org.apache.commons.math3.optim.OptimizationData;
import org.apache.commons.math3.exception.NumberIsTooLargeException;
import org.apache.commons.math3.exception.OutOfRangeException;

/**
 * Search interval and (optional) start value.
 * <br/>
 * Immutable class.
 *
 * @since 3.1
 */
public class SearchInterval implements OptimizationData {
    /** Lower bound. */
    private final double lower;
    /** Upper bound. */
    private final double upper;
    /** Start value. */
    private final double start;

    /**
     * @param lo Lower bound.
     * @param hi Upper bound.
     * @param init Start value.
     * @throws NumberIsTooLargeException if {@code lo >= hi}.
     * @throws OutOfRangeException if {@code init < lo} or {@code init > hi}.
     */
    public SearchInterval(double lo,
                          double hi,
                          double init) {
        if (lo >= hi) {
            throw new NumberIsTooLargeException(lo, hi, false);
        }
        if (init < lo ||
            init > hi) {
            throw new OutOfRangeException(init, lo, hi);
        }

        lower = lo;
        upper = hi;
        start = init;
    }

    /**
     * @param lo Lower bound.
     * @param hi Upper bound.
     * @throws NumberIsTooLargeException if {@code lo >= hi}.
     */
    public SearchInterval(double lo,
                          double hi) {
        this(lo, hi, 0.5 * (lo + hi));
    }

    /**
     * Gets the lower bound.
     *
     * @return the lower bound.
     */
    public double getMin() {
        return lower;
    }
    /**
     * Gets the upper bound.
     *
     * @return the upper bound.
     */
    public double getMax() {
        return upper;
    }
    /**
     * Gets the start value.
     *
     * @return the start value.
     */
    public double getStartValue() {
        return start;
    }
}
