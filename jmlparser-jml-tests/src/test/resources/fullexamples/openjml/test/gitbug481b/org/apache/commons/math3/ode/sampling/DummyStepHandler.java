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

/**
 * This class is a step handler that does nothing.

 * <p>This class is provided as a convenience for users who are only
 * interested in the final state of an integration and not in the
 * intermediate steps. Its handleStep method does nothing.</p>
 *
 * <p>Since this class has no internal state, it is implemented using
 * the Singleton design pattern. This means that only one instance is
 * ever created, which can be retrieved using the getInstance
 * method. This explains why there is no public constructor.</p>
 *
 * @see StepHandler
 * @since 1.2
 */

public class DummyStepHandler implements StepHandler {

    /** Private constructor.
     * The constructor is private to prevent users from creating
     * instances (Singleton design-pattern).
     */
    private DummyStepHandler() {
    }

    /** Get the only instance.
     * @return the only instance
     */
    public static DummyStepHandler getInstance() {
        return LazyHolder.INSTANCE;
    }

    /** {@inheritDoc} */
    public void init(double t0, double[] y0, double t) {
    }

    /**
     * Handle the last accepted step.
     * This method does nothing in this class.
     * @param interpolator interpolator for the last accepted step. For
     * efficiency purposes, the various integrators reuse the same
     * object on each call, so if the instance wants to keep it across
     * all calls (for example to provide at the end of the integration a
     * continuous model valid throughout the integration range), it
     * should build a local copy using the clone method and store this
     * copy.
     * @param isLast true if the step is the last one
     */
    public void handleStep(final StepInterpolator interpolator, final boolean isLast) {
    }

    // CHECKSTYLE: stop HideUtilityClassConstructor
    /** Holder for the instance.
     * <p>We use here the Initialization On Demand Holder Idiom.</p>
     */
    private static class LazyHolder {
        /** Cached field instance. */
        private static final DummyStepHandler INSTANCE = new DummyStepHandler();
    }
    // CHECKSTYLE: resume HideUtilityClassConstructor

    /** Handle deserialization of the singleton.
     * @return the singleton instance
     */
    private Object readResolve() {
        // return the singleton instance
        return LazyHolder.INSTANCE;
    }

}
