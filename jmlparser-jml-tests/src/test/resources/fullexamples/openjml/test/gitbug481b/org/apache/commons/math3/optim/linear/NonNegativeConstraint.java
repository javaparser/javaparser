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
package org.apache.commons.math3.optim.linear;

import org.apache.commons.math3.optim.OptimizationData;

/**
 * A constraint for a linear optimization problem indicating whether all
 * variables must be restricted to non-negative values.
 *
 * @since 3.1
 */
public class NonNegativeConstraint implements OptimizationData {
    /** Whether the variables are all positive. */
    private final boolean isRestricted;

    /**
     * @param restricted If {@code true}, all the variables must be positive.
     */
    public NonNegativeConstraint(boolean restricted) {
        isRestricted = restricted;
    }

    /**
     * Indicates whether all the variables must be restricted to non-negative
     * values.
     *
     * @return {@code true} if all the variables must be positive.
     */
    public boolean isRestrictedToNonNegative() {
        return isRestricted;
    }
}
