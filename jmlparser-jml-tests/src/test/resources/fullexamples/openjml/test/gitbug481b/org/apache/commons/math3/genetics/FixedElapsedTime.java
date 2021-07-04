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
package org.apache.commons.math3.genetics;

import java.util.concurrent.TimeUnit;

import org.apache.commons.math3.exception.NumberIsTooSmallException;

/**
 * Stops after a fixed amount of time has elapsed.
 * <p>
 * The first time {@link #isSatisfied(Population)} is invoked, the end time of the evolution is determined based on the
 * provided <code>maxTime</code> value. Once the elapsed time reaches the configured <code>maxTime</code> value,
 * {@link #isSatisfied(Population)} returns true.
 *
 * @since 3.1
 */
public class FixedElapsedTime implements StoppingCondition {
    /** Maximum allowed time period (in nanoseconds). */
    private final long maxTimePeriod;

    /** The predetermined termination time (stopping condition). */
    private long endTime = -1;

    /**
     * Create a new {@link FixedElapsedTime} instance.
     *
     * @param maxTime maximum number of seconds generations are allowed to evolve
     * @throws NumberIsTooSmallException if the provided time is &lt; 0
     */
    public FixedElapsedTime(final long maxTime) throws NumberIsTooSmallException {
        this(maxTime, TimeUnit.SECONDS);
    }

    /**
     * Create a new {@link FixedElapsedTime} instance.
     *
     * @param maxTime maximum time generations are allowed to evolve
     * @param unit {@link TimeUnit} of the maxTime argument
     * @throws NumberIsTooSmallException if the provided time is &lt; 0
     */
    public FixedElapsedTime(final long maxTime, final TimeUnit unit) throws NumberIsTooSmallException {
        if (maxTime < 0) {
            throw new NumberIsTooSmallException(maxTime, 0, true);
        }
        maxTimePeriod = unit.toNanos(maxTime);
    }

    /**
     * Determine whether or not the maximum allowed time has passed.
     * The termination time is determined after the first generation.
     *
     * @param population ignored (no impact on result)
     * @return <code>true</code> IFF the maximum allowed time period has elapsed
     */
    public boolean isSatisfied(final Population population) {
        if (endTime < 0) {
            endTime = System.nanoTime() + maxTimePeriod;
        }

        return System.nanoTime() >= endTime;
    }
}
