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

package org.apache.commons.math3.ode.sampling;

/** {@link StepNormalizer Step normalizer} bounds settings. They influence
 * whether the underlying fixed step size step handler is called for the first
 * and last points. Note that if the last point coincides with a normalized
 * point, then the underlying fixed step size step handler is always called,
 * regardless of these settings.
 * @see FieldStepNormalizer
 * @see StepNormalizer
 * @see StepNormalizerMode
 * @since 3.0
 */
public enum StepNormalizerBounds {
    /** Do not include the first and last points. */
    NEITHER(false, false),

    /** Include the first point, but not the last point. */
    FIRST(true, false),

    /** Include the last point, but not the first point. */
    LAST(false, true),

    /** Include both the first and last points. */
    BOTH(true, true);

    /** Whether the first point should be passed to the underlying fixed
     * step size step handler.
     */
    private final boolean first;

    /** Whether the last point should be passed to the underlying fixed
     * step size step handler.
     */
    private final boolean last;

    /**
     * Simple constructor.
     * @param first Whether the first point should be passed to the
     * underlying fixed step size step handler.
     * @param last Whether the last point should be passed to the
     * underlying fixed step size step handler.
     */
    StepNormalizerBounds(final boolean first, final boolean last) {
        this.first = first;
        this.last = last;
    }

    /**
     * Returns a value indicating whether the first point should be passed
     * to the underlying fixed step size step handler.
     * @return value indicating whether the first point should be passed
     * to the underlying fixed step size step handler.
     */
    public boolean firstIncluded() {
        return first;
    }

    /**
     * Returns a value indicating whether the last point should be passed
     * to the underlying fixed step size step handler.
     * @return value indicating whether the last point should be passed
     * to the underlying fixed step size step handler.
     */
    public boolean lastIncluded() {
        return last;
    }
}
