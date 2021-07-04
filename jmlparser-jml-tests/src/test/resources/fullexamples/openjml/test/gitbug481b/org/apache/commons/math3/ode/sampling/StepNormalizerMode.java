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


/** {@link StepNormalizer Step normalizer} modes. Determines how the step size
 * is interpreted.
 * @see FieldStepNormalizer
 * @see StepNormalizer
 * @see StepNormalizerBounds
 * @since 3.0
 */
public enum StepNormalizerMode {
    /**
     * Steps are fixed increments of the start value. In other words, they
     * are relative to the start value.
     *
     * <p>If the integration start time is t0, then the points handled by
     * the underlying fixed step size step handler are t0 (depending on
     * the {@link StepNormalizerBounds bounds settings}), t0+h, t0+2h, ...</p>
     *
     * <p>If the integration range is an integer multiple of the step size
     * (h), then the last point handled will be the end point of the
     * integration (tend). If not, the last point may be the end point
     * tend, or it may be a point belonging to the interval [tend - h ;
     * tend], depending on the {@link StepNormalizerBounds bounds settings}.
     * </p>
     *
     * @see StepNormalizer
     * @see StepNormalizerBounds
     */
    INCREMENT,

    /** Steps are multiples of a fixed value. In other words, they are
     * relative to the first multiple of the step size that is encountered
     * after the start value.
     *
     * <p>If the integration start time is t0, and the first multiple of
     * the fixed step size that is encountered is t1, then the points
     * handled by the underlying fixed step size step handler are t0
     * (depending on the {@link StepNormalizerBounds bounds settings}), t1,
     * t1+h, t1+2h, ...</p>
     *
     * <p>If the end point of the integration range (tend) is an integer
     * multiple of the step size (h) added to t1, then the last point
     * handled will be the end point of the integration (tend). If not,
     * the last point may be the end point tend, or it may be a point
     * belonging to the interval [tend - h ; tend], depending on the
     * {@link StepNormalizerBounds bounds settings}.</p>
     *
     * @see StepNormalizer
     * @see StepNormalizerBounds
     */
    MULTIPLES;
}
