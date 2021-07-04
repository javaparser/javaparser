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

import org.apache.commons.math3.RealFieldElement;
import org.apache.commons.math3.exception.MaxCountExceededException;
import org.apache.commons.math3.ode.FieldODEStateAndDerivative;
import org.apache.commons.math3.util.FastMath;
import org.apache.commons.math3.util.Precision;

/**
 * This class wraps an object implementing {@link FieldFixedStepHandler}
 * into a {@link FieldStepHandler}.

 * <p>This wrapper allows to use fixed step handlers with general
 * integrators which cannot guaranty their integration steps will
 * remain constant and therefore only accept general step
 * handlers.</p>
 *
 * <p>The stepsize used is selected at construction time. The {@link
 * FieldFixedStepHandler#handleStep handleStep} method of the underlying
 * {@link FieldFixedStepHandler} object is called at normalized times. The
 * normalized times can be influenced by the {@link StepNormalizerMode} and
 * {@link StepNormalizerBounds}.</p>
 *
 * <p>There is no constraint on the integrator, it can use any time step
 * it needs (time steps longer or shorter than the fixed time step and
 * non-integer ratios are all allowed).</p>
 *
 * <p>
 * <table border="1" align="center">
 * <tr BGCOLOR="#CCCCFF"><td colspan=6><font size="+2">Examples (step size = 0.5)</font></td></tr>
 * <tr BGCOLOR="#EEEEFF"><font size="+1"><td>Start time</td><td>End time</td>
 *  <td>Direction</td><td>{@link StepNormalizerMode Mode}</td>
 *  <td>{@link StepNormalizerBounds Bounds}</td><td>Output</td></font></tr>
 * <tr><td>0.3</td><td>3.1</td><td>forward</td><td>{@link StepNormalizerMode#INCREMENT INCREMENT}</td><td>{@link StepNormalizerBounds#NEITHER NEITHER}</td><td>0.8, 1.3, 1.8, 2.3, 2.8</td></tr>
 * <tr><td>0.3</td><td>3.1</td><td>forward</td><td>{@link StepNormalizerMode#INCREMENT INCREMENT}</td><td>{@link StepNormalizerBounds#FIRST FIRST}</td><td>0.3, 0.8, 1.3, 1.8, 2.3, 2.8</td></tr>
 * <tr><td>0.3</td><td>3.1</td><td>forward</td><td>{@link StepNormalizerMode#INCREMENT INCREMENT}</td><td>{@link StepNormalizerBounds#LAST LAST}</td><td>0.8, 1.3, 1.8, 2.3, 2.8, 3.1</td></tr>
 * <tr><td>0.3</td><td>3.1</td><td>forward</td><td>{@link StepNormalizerMode#INCREMENT INCREMENT}</td><td>{@link StepNormalizerBounds#BOTH BOTH}</td><td>0.3, 0.8, 1.3, 1.8, 2.3, 2.8, 3.1</td></tr>
 * <tr><td>0.3</td><td>3.1</td><td>forward</td><td>{@link StepNormalizerMode#MULTIPLES MULTIPLES}</td><td>{@link StepNormalizerBounds#NEITHER NEITHER}</td><td>0.5, 1.0, 1.5, 2.0, 2.5, 3.0</td></tr>
 * <tr><td>0.3</td><td>3.1</td><td>forward</td><td>{@link StepNormalizerMode#MULTIPLES MULTIPLES}</td><td>{@link StepNormalizerBounds#FIRST FIRST}</td><td>0.3, 0.5, 1.0, 1.5, 2.0, 2.5, 3.0</td></tr>
 * <tr><td>0.3</td><td>3.1</td><td>forward</td><td>{@link StepNormalizerMode#MULTIPLES MULTIPLES}</td><td>{@link StepNormalizerBounds#LAST LAST}</td><td>0.5, 1.0, 1.5, 2.0, 2.5, 3.0, 3.1</td></tr>
 * <tr><td>0.3</td><td>3.1</td><td>forward</td><td>{@link StepNormalizerMode#MULTIPLES MULTIPLES}</td><td>{@link StepNormalizerBounds#BOTH BOTH}</td><td>0.3, 0.5, 1.0, 1.5, 2.0, 2.5, 3.0, 3.1</td></tr>
 * <tr><td>0.0</td><td>3.0</td><td>forward</td><td>{@link StepNormalizerMode#INCREMENT INCREMENT}</td><td>{@link StepNormalizerBounds#NEITHER NEITHER}</td><td>0.5, 1.0, 1.5, 2.0, 2.5, 3.0</td></tr>
 * <tr><td>0.0</td><td>3.0</td><td>forward</td><td>{@link StepNormalizerMode#INCREMENT INCREMENT}</td><td>{@link StepNormalizerBounds#FIRST FIRST}</td><td>0.0, 0.5, 1.0, 1.5, 2.0, 2.5, 3.0</td></tr>
 * <tr><td>0.0</td><td>3.0</td><td>forward</td><td>{@link StepNormalizerMode#INCREMENT INCREMENT}</td><td>{@link StepNormalizerBounds#LAST LAST}</td><td>0.5, 1.0, 1.5, 2.0, 2.5, 3.0</td></tr>
 * <tr><td>0.0</td><td>3.0</td><td>forward</td><td>{@link StepNormalizerMode#INCREMENT INCREMENT}</td><td>{@link StepNormalizerBounds#BOTH BOTH}</td><td>0.0, 0.5, 1.0, 1.5, 2.0, 2.5, 3.0</td></tr>
 * <tr><td>0.0</td><td>3.0</td><td>forward</td><td>{@link StepNormalizerMode#MULTIPLES MULTIPLES}</td><td>{@link StepNormalizerBounds#NEITHER NEITHER}</td><td>0.5, 1.0, 1.5, 2.0, 2.5, 3.0</td></tr>
 * <tr><td>0.0</td><td>3.0</td><td>forward</td><td>{@link StepNormalizerMode#MULTIPLES MULTIPLES}</td><td>{@link StepNormalizerBounds#FIRST FIRST}</td><td>0.0, 0.5, 1.0, 1.5, 2.0, 2.5, 3.0</td></tr>
 * <tr><td>0.0</td><td>3.0</td><td>forward</td><td>{@link StepNormalizerMode#MULTIPLES MULTIPLES}</td><td>{@link StepNormalizerBounds#LAST LAST}</td><td>0.5, 1.0, 1.5, 2.0, 2.5, 3.0</td></tr>
 * <tr><td>0.0</td><td>3.0</td><td>forward</td><td>{@link StepNormalizerMode#MULTIPLES MULTIPLES}</td><td>{@link StepNormalizerBounds#BOTH BOTH}</td><td>0.0, 0.5, 1.0, 1.5, 2.0, 2.5, 3.0</td></tr>
 * <tr><td>3.1</td><td>0.3</td><td>backward</td><td>{@link StepNormalizerMode#INCREMENT INCREMENT}</td><td>{@link StepNormalizerBounds#NEITHER NEITHER}</td><td>2.6, 2.1, 1.6, 1.1, 0.6</td></tr>
 * <tr><td>3.1</td><td>0.3</td><td>backward</td><td>{@link StepNormalizerMode#INCREMENT INCREMENT}</td><td>{@link StepNormalizerBounds#FIRST FIRST}</td><td>3.1, 2.6, 2.1, 1.6, 1.1, 0.6</td></tr>
 * <tr><td>3.1</td><td>0.3</td><td>backward</td><td>{@link StepNormalizerMode#INCREMENT INCREMENT}</td><td>{@link StepNormalizerBounds#LAST LAST}</td><td>2.6, 2.1, 1.6, 1.1, 0.6, 0.3</td></tr>
 * <tr><td>3.1</td><td>0.3</td><td>backward</td><td>{@link StepNormalizerMode#INCREMENT INCREMENT}</td><td>{@link StepNormalizerBounds#BOTH BOTH}</td><td>3.1, 2.6, 2.1, 1.6, 1.1, 0.6, 0.3</td></tr>
 * <tr><td>3.1</td><td>0.3</td><td>backward</td><td>{@link StepNormalizerMode#MULTIPLES MULTIPLES}</td><td>{@link StepNormalizerBounds#NEITHER NEITHER}</td><td>3.0, 2.5, 2.0, 1.5, 1.0, 0.5</td></tr>
 * <tr><td>3.1</td><td>0.3</td><td>backward</td><td>{@link StepNormalizerMode#MULTIPLES MULTIPLES}</td><td>{@link StepNormalizerBounds#FIRST FIRST}</td><td>3.1, 3.0, 2.5, 2.0, 1.5, 1.0, 0.5</td></tr>
 * <tr><td>3.1</td><td>0.3</td><td>backward</td><td>{@link StepNormalizerMode#MULTIPLES MULTIPLES}</td><td>{@link StepNormalizerBounds#LAST LAST}</td><td>3.0, 2.5, 2.0, 1.5, 1.0, 0.5, 0.3</td></tr>
 * <tr><td>3.1</td><td>0.3</td><td>backward</td><td>{@link StepNormalizerMode#MULTIPLES MULTIPLES}</td><td>{@link StepNormalizerBounds#BOTH BOTH}</td><td>3.1, 3.0, 2.5, 2.0, 1.5, 1.0, 0.5, 0.3</td></tr>
 * <tr><td>3.0</td><td>0.0</td><td>backward</td><td>{@link StepNormalizerMode#INCREMENT INCREMENT}</td><td>{@link StepNormalizerBounds#NEITHER NEITHER}</td><td>2.5, 2.0, 1.5, 1.0, 0.5, 0.0</td></tr>
 * <tr><td>3.0</td><td>0.0</td><td>backward</td><td>{@link StepNormalizerMode#INCREMENT INCREMENT}</td><td>{@link StepNormalizerBounds#FIRST FIRST}</td><td>3.0, 2.5, 2.0, 1.5, 1.0, 0.5, 0.0</td></tr>
 * <tr><td>3.0</td><td>0.0</td><td>backward</td><td>{@link StepNormalizerMode#INCREMENT INCREMENT}</td><td>{@link StepNormalizerBounds#LAST LAST}</td><td>2.5, 2.0, 1.5, 1.0, 0.5, 0.0</td></tr>
 * <tr><td>3.0</td><td>0.0</td><td>backward</td><td>{@link StepNormalizerMode#INCREMENT INCREMENT}</td><td>{@link StepNormalizerBounds#BOTH BOTH}</td><td>3.0, 2.5, 2.0, 1.5, 1.0, 0.5, 0.0</td></tr>
 * <tr><td>3.0</td><td>0.0</td><td>backward</td><td>{@link StepNormalizerMode#MULTIPLES MULTIPLES}</td><td>{@link StepNormalizerBounds#NEITHER NEITHER}</td><td>2.5, 2.0, 1.5, 1.0, 0.5, 0.0</td></tr>
 * <tr><td>3.0</td><td>0.0</td><td>backward</td><td>{@link StepNormalizerMode#MULTIPLES MULTIPLES}</td><td>{@link StepNormalizerBounds#FIRST FIRST}</td><td>3.0, 2.5, 2.0, 1.5, 1.0, 0.5, 0.0</td></tr>
 * <tr><td>3.0</td><td>0.0</td><td>backward</td><td>{@link StepNormalizerMode#MULTIPLES MULTIPLES}</td><td>{@link StepNormalizerBounds#LAST LAST}</td><td>2.5, 2.0, 1.5, 1.0, 0.5, 0.0</td></tr>
 * <tr><td>3.0</td><td>0.0</td><td>backward</td><td>{@link StepNormalizerMode#MULTIPLES MULTIPLES}</td><td>{@link StepNormalizerBounds#BOTH BOTH}</td><td>3.0, 2.5, 2.0, 1.5, 1.0, 0.5, 0.0</td></tr>
 * </table>
 * </p>
 *
 * @param <T> the type of the field elements
 * @see FieldStepHandler
 * @see FieldFixedStepHandler
 * @see StepNormalizerMode
 * @see StepNormalizerBounds
 * @since 3.6
 */

public class FieldStepNormalizer<T extends RealFieldElement<T>> implements FieldStepHandler<T> {

    /** Fixed time step. */
    private double h;

    /** Underlying step handler. */
    private final FieldFixedStepHandler<T> handler;

    /** First step state. */
    private FieldODEStateAndDerivative<T> first;

    /** Last step step. */
    private FieldODEStateAndDerivative<T> last;

    /** Integration direction indicator. */
    private boolean forward;

    /** The step normalizer bounds settings to use. */
    private final StepNormalizerBounds bounds;

    /** The step normalizer mode to use. */
    private final StepNormalizerMode mode;

    /** Simple constructor. Uses {@link StepNormalizerMode#INCREMENT INCREMENT}
     * mode, and {@link StepNormalizerBounds#FIRST FIRST} bounds setting, for
     * backwards compatibility.
     * @param h fixed time step (sign is not used)
     * @param handler fixed time step handler to wrap
     */
    public FieldStepNormalizer(final double h, final FieldFixedStepHandler<T> handler) {
        this(h, handler, StepNormalizerMode.INCREMENT,
             StepNormalizerBounds.FIRST);
    }

    /** Simple constructor. Uses {@link StepNormalizerBounds#FIRST FIRST}
     * bounds setting.
     * @param h fixed time step (sign is not used)
     * @param handler fixed time step handler to wrap
     * @param mode step normalizer mode to use
     * @since 3.0
     */
    public FieldStepNormalizer(final double h, final FieldFixedStepHandler<T> handler,
                               final StepNormalizerMode mode) {
        this(h, handler, mode, StepNormalizerBounds.FIRST);
    }

    /** Simple constructor. Uses {@link StepNormalizerMode#INCREMENT INCREMENT}
     * mode.
     * @param h fixed time step (sign is not used)
     * @param handler fixed time step handler to wrap
     * @param bounds step normalizer bounds setting to use
     * @since 3.0
     */
    public FieldStepNormalizer(final double h, final FieldFixedStepHandler<T> handler,
                               final StepNormalizerBounds bounds) {
        this(h, handler, StepNormalizerMode.INCREMENT, bounds);
    }

    /** Simple constructor.
     * @param h fixed time step (sign is not used)
     * @param handler fixed time step handler to wrap
     * @param mode step normalizer mode to use
     * @param bounds step normalizer bounds setting to use
     * @since 3.0
     */
    public FieldStepNormalizer(final double h, final FieldFixedStepHandler<T> handler,
                               final StepNormalizerMode mode, final StepNormalizerBounds bounds) {
        this.h       = FastMath.abs(h);
        this.handler = handler;
        this.mode    = mode;
        this.bounds  = bounds;
        first        = null;
        last         = null;
        forward      = true;
    }

    /** {@inheritDoc} */
    public void init(final FieldODEStateAndDerivative<T> initialState, final T finalTime) {

        first   = null;
        last    = null;
        forward = true;

        // initialize the underlying handler
        handler.init(initialState, finalTime);

    }

    /**
     * Handle the last accepted step
     * @param interpolator interpolator for the last accepted step. For
     * efficiency purposes, the various integrators reuse the same
     * object on each call, so if the instance wants to keep it across
     * all calls (for example to provide at the end of the integration a
     * continuous model valid throughout the integration range), it
     * should build a local copy using the clone method and store this
     * copy.
     * @param isLast true if the step is the last one
     * @exception MaxCountExceededException if the interpolator throws one because
     * the number of functions evaluations is exceeded
     */
    public void handleStep(final FieldStepInterpolator<T> interpolator, final boolean isLast)
        throws MaxCountExceededException {
        // The first time, update the last state with the start information.
        if (last == null) {

            first   = interpolator.getPreviousState();
            last    = first;

            // Take the integration direction into account.
            forward = interpolator.isForward();
            if (!forward) {
                h = -h;
            }
        }

        // Calculate next normalized step time.
        T nextTime = (mode == StepNormalizerMode.INCREMENT) ?
                     last.getTime().add(h) :
                     last.getTime().getField().getZero().add((FastMath.floor(last.getTime().getReal() / h) + 1) * h);
        if (mode == StepNormalizerMode.MULTIPLES &&
            Precision.equals(nextTime.getReal(), last.getTime().getReal(), 1)) {
            nextTime = nextTime.add(h);
        }

        // Process normalized steps as long as they are in the current step.
        boolean nextInStep = isNextInStep(nextTime, interpolator);
        while (nextInStep) {
            // Output the stored previous step.
            doNormalizedStep(false);

            // Store the next step as last step.
            last = interpolator.getInterpolatedState(nextTime);

            // Move on to the next step.
            nextTime = nextTime.add(h);
            nextInStep = isNextInStep(nextTime, interpolator);
        }

        if (isLast) {
            // There will be no more steps. The stored one should be given to
            // the handler. We may have to output one more step. Only the last
            // one of those should be flagged as being the last.
            final boolean addLast = bounds.lastIncluded() &&
                                    last.getTime().getReal() != interpolator.getCurrentState().getTime().getReal();
            doNormalizedStep(!addLast);
            if (addLast) {
                last = interpolator.getCurrentState();
                doNormalizedStep(true);
            }
        }
    }

    /**
     * Returns a value indicating whether the next normalized time is in the
     * current step.
     * @param nextTime the next normalized time
     * @param interpolator interpolator for the last accepted step, to use to
     * get the end time of the current step
     * @return value indicating whether the next normalized time is in the
     * current step
     */
    private boolean isNextInStep(final T nextTime, final FieldStepInterpolator<T> interpolator) {
        return forward ?
               nextTime.getReal() <= interpolator.getCurrentState().getTime().getReal() :
               nextTime.getReal() >= interpolator.getCurrentState().getTime().getReal();
    }

    /**
     * Invokes the underlying step handler for the current normalized step.
     * @param isLast true if the step is the last one
     */
    private void doNormalizedStep(final boolean isLast) {
        if (!bounds.firstIncluded() && first.getTime().getReal() == last.getTime().getReal()) {
            return;
        }
        handler.handleStep(last, isLast);
    }

}
