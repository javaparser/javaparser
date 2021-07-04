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

/**
 * Simple optimization constraints: lower and upper bounds.
 * The valid range of the parameters is an interval that can be infinite
 * (in one or both directions).
 * <br/>
 * Immutable class.
 *
 * @deprecated As of 3.1 (to be removed in 4.0).
 * @since 3.1
 */
@Deprecated
public class SimpleBounds implements OptimizationData {
    /** Lower bounds. */
    private final double[] lower;
    /** Upper bounds. */
    private final double[] upper;

    /**
     * @param lB Lower bounds.
     * @param uB Upper bounds.
     */
    public SimpleBounds(double[] lB,
                        double[] uB) {
        lower = lB.clone();
        upper = uB.clone();
    }

    /**
     * Gets the lower bounds.
     *
     * @return the initial guess.
     */
    public double[] getLower() {
        return lower.clone();
    }
    /**
     * Gets the lower bounds.
     *
     * @return the initial guess.
     */
    public double[] getUpper() {
        return upper.clone();
    }
}
