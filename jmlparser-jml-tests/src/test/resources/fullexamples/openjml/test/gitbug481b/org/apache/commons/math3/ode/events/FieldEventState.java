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

package org.apache.commons.math3.ode.events;

import org.apache.commons.math3.RealFieldElement;
import org.apache.commons.math3.analysis.RealFieldUnivariateFunction;
import org.apache.commons.math3.analysis.solvers.AllowedSolution;
import org.apache.commons.math3.analysis.solvers.BracketedRealFieldUnivariateSolver;
import org.apache.commons.math3.exception.MaxCountExceededException;
import org.apache.commons.math3.exception.NoBracketingException;
import org.apache.commons.math3.ode.FieldODEState;
import org.apache.commons.math3.ode.FieldODEStateAndDerivative;
import org.apache.commons.math3.ode.sampling.FieldStepInterpolator;
import org.apache.commons.math3.util.FastMath;

/** This class handles the state for one {@link EventHandler
 * event handler} during integration steps.
 *
 * <p>Each time the integrator proposes a step, the event handler
 * switching function should be checked. This class handles the state
 * of one handler during one integration step, with references to the
 * state at the end of the preceding step. This information is used to
 * decide if the handler should trigger an event or not during the
 * proposed step.</p>
 *
 * @param <T> the type of the field elements
 * @since 3.6
 */
public class FieldEventState<T extends RealFieldElement<T>> {

    /** Event handler. */
    private final FieldEventHandler<T> handler;

    /** Maximal time interval between events handler checks. */
    private final double maxCheckInterval;

    /** Convergence threshold for event localization. */
    private final T convergence;

    /** Upper limit in the iteration count for event localization. */
    private final int maxIterationCount;

    /** Time at the beginning of the step. */
    private T t0;

    /** Value of the events handler at the beginning of the step. */
    private T g0;

    /** Simulated sign of g0 (we cheat when crossing events). */
    private boolean g0Positive;

    /** Indicator of event expected during the step. */
    private boolean pendingEvent;

    /** Occurrence time of the pending event. */
    private T pendingEventTime;

    /** Occurrence time of the previous event. */
    private T previousEventTime;

    /** Integration direction. */
    private boolean forward;

    /** Variation direction around pending event.
     *  (this is considered with respect to the integration direction)
     */
    private boolean increasing;

    /** Next action indicator. */
    private Action nextAction;

    /** Root-finding algorithm to use to detect state events. */
    private final BracketedRealFieldUnivariateSolver<T> solver;

    /** Simple constructor.
     * @param handler event handler
     * @param maxCheckInterval maximal time interval between switching
     * function checks (this interval prevents missing sign changes in
     * case the integration steps becomes very large)
     * @param convergence convergence threshold in the event time search
     * @param maxIterationCount upper limit of the iteration count in
     * the event time search
     * @param solver Root-finding algorithm to use to detect state events
     */
    public FieldEventState(final FieldEventHandler<T> handler, final double maxCheckInterval,
                           final T convergence, final int maxIterationCount,
                           final BracketedRealFieldUnivariateSolver<T> solver) {
        this.handler           = handler;
        this.maxCheckInterval  = maxCheckInterval;
        this.convergence       = convergence.abs();
        this.maxIterationCount = maxIterationCount;
        this.solver            = solver;

        // some dummy values ...
        t0                = null;
        g0                = null;
        g0Positive        = true;
        pendingEvent      = false;
        pendingEventTime  = null;
        previousEventTime = null;
        increasing        = true;
        nextAction        = Action.CONTINUE;

    }

    /** Get the underlying event handler.
     * @return underlying event handler
     */
    public FieldEventHandler<T> getEventHandler() {
        return handler;
    }

    /** Get the maximal time interval between events handler checks.
     * @return maximal time interval between events handler checks
     */
    public double getMaxCheckInterval() {
        return maxCheckInterval;
    }

    /** Get the convergence threshold for event localization.
     * @return convergence threshold for event localization
     */
    public T getConvergence() {
        return convergence;
    }

    /** Get the upper limit in the iteration count for event localization.
     * @return upper limit in the iteration count for event localization
     */
    public int getMaxIterationCount() {
        return maxIterationCount;
    }

    /** Reinitialize the beginning of the step.
     * @param interpolator valid for the current step
     * @exception MaxCountExceededException if the interpolator throws one because
     * the number of functions evaluations is exceeded
     */
    public void reinitializeBegin(final FieldStepInterpolator<T> interpolator)
        throws MaxCountExceededException {

        final FieldODEStateAndDerivative<T> s0 = interpolator.getPreviousState();
        t0 = s0.getTime();
        g0 = handler.g(s0);
        if (g0.getReal() == 0) {
            // excerpt from MATH-421 issue:
            // If an ODE solver is setup with an EventHandler that return STOP
            // when the even is triggered, the integrator stops (which is exactly
            // the expected behavior). If however the user wants to restart the
            // solver from the final state reached at the event with the same
            // configuration (expecting the event to be triggered again at a
            // later time), then the integrator may fail to start. It can get stuck
            // at the previous event. The use case for the bug MATH-421 is fairly
            // general, so events occurring exactly at start in the first step should
            // be ignored.

            // extremely rare case: there is a zero EXACTLY at interval start
            // we will use the sign slightly after step beginning to force ignoring this zero
            final double epsilon = FastMath.max(solver.getAbsoluteAccuracy().getReal(),
                                                FastMath.abs(solver.getRelativeAccuracy().multiply(t0).getReal()));
            final T tStart = t0.add(0.5 * epsilon);
            g0 = handler.g(interpolator.getInterpolatedState(tStart));
        }
        g0Positive = g0.getReal() >= 0;

    }

    /** Evaluate the impact of the proposed step on the event handler.
     * @param interpolator step interpolator for the proposed step
     * @return true if the event handler triggers an event before
     * the end of the proposed step
     * @exception MaxCountExceededException if the interpolator throws one because
     * the number of functions evaluations is exceeded
     * @exception NoBracketingException if the event cannot be bracketed
     */
    public boolean evaluateStep(final FieldStepInterpolator<T> interpolator)
        throws MaxCountExceededException, NoBracketingException {

        forward = interpolator.isForward();
        final FieldODEStateAndDerivative<T> s1 = interpolator.getCurrentState();
        final T t1 = s1.getTime();
        final T dt = t1.subtract(t0);
        if (dt.abs().subtract(convergence).getReal() < 0) {
            // we cannot do anything on such a small step, don't trigger any events
            return false;
        }
        final int n = FastMath.max(1, (int) FastMath.ceil(FastMath.abs(dt.getReal()) / maxCheckInterval));
        final T   h = dt.divide(n);

        final RealFieldUnivariateFunction<T> f = new RealFieldUnivariateFunction<T>() {
            /** {@inheritDoc} */
            public T value(final T t) {
                return handler.g(interpolator.getInterpolatedState(t));
            }
        };

        T ta = t0;
        T ga = g0;
        for (int i = 0; i < n; ++i) {

            // evaluate handler value at the end of the substep
            final T tb = (i == n - 1) ? t1 : t0.add(h.multiply(i + 1));
            final T gb = handler.g(interpolator.getInterpolatedState(tb));

            // check events occurrence
            if (g0Positive ^ (gb.getReal() >= 0)) {
                // there is a sign change: an event is expected during this step

                // variation direction, with respect to the integration direction
                increasing = gb.subtract(ga).getReal() >= 0;

                // find the event time making sure we select a solution just at or past the exact root
                final T root = forward ?
                               solver.solve(maxIterationCount, f, ta, tb, AllowedSolution.RIGHT_SIDE) :
                               solver.solve(maxIterationCount, f, tb, ta, AllowedSolution.LEFT_SIDE);

                if (previousEventTime != null &&
                    root.subtract(ta).abs().subtract(convergence).getReal() <= 0 &&
                    root.subtract(previousEventTime).abs().subtract(convergence).getReal() <= 0) {
                    // we have either found nothing or found (again ?) a past event,
                    // retry the substep excluding this value, and taking care to have the
                    // required sign in case the g function is noisy around its zero and
                    // crosses the axis several times
                    do {
                        ta = forward ? ta.add(convergence) : ta.subtract(convergence);
                        ga = f.value(ta);
                    } while ((g0Positive ^ (ga.getReal() >= 0)) && (forward ^ (ta.subtract(tb).getReal() >= 0)));

                    if (forward ^ (ta.subtract(tb).getReal() >= 0)) {
                        // we were able to skip this spurious root
                        --i;
                    } else {
                        // we can't avoid this root before the end of the step,
                        // we have to handle it despite it is close to the former one
                        // maybe we have two very close roots
                        pendingEventTime = root;
                        pendingEvent     = true;
                        return true;
                    }
                } else if (previousEventTime == null ||
                           previousEventTime.subtract(root).abs().subtract(convergence).getReal() > 0) {
                    pendingEventTime = root;
                    pendingEvent     = true;
                    return true;
                } else {
                    // no sign change: there is no event for now
                    ta = tb;
                    ga = gb;
                }

            } else {
                // no sign change: there is no event for now
                ta = tb;
                ga = gb;
            }

        }

        // no event during the whole step
        pendingEvent     = false;
        pendingEventTime = null;
        return false;

    }

    /** Get the occurrence time of the event triggered in the current step.
     * @return occurrence time of the event triggered in the current
     * step or infinity if no events are triggered
     */
    public T getEventTime() {
        return pendingEvent ?
               pendingEventTime :
               t0.getField().getZero().add(forward ? Double.POSITIVE_INFINITY : Double.NEGATIVE_INFINITY);
    }

    /** Acknowledge the fact the step has been accepted by the integrator.
     * @param state state at the end of the step
     */
    public void stepAccepted(final FieldODEStateAndDerivative<T> state) {

        t0 = state.getTime();
        g0 = handler.g(state);

        if (pendingEvent && pendingEventTime.subtract(state.getTime()).abs().subtract(convergence).getReal() <= 0) {
            // force the sign to its value "just after the event"
            previousEventTime = state.getTime();
            g0Positive        = increasing;
            nextAction        = handler.eventOccurred(state, !(increasing ^ forward));
        } else {
            g0Positive = g0.getReal() >= 0;
            nextAction = Action.CONTINUE;
        }
    }

    /** Check if the integration should be stopped at the end of the
     * current step.
     * @return true if the integration should be stopped
     */
    public boolean stop() {
        return nextAction == Action.STOP;
    }

    /** Let the event handler reset the state if it wants.
     * @param state state at the beginning of the next step
     * @return reset state (may by the same as initial state if only
     * derivatives should be reset), or null if nothing is reset
     */
    public FieldODEState<T> reset(final FieldODEStateAndDerivative<T> state) {

        if (!(pendingEvent && pendingEventTime.subtract(state.getTime()).abs().subtract(convergence).getReal() <= 0)) {
            return null;
        }

        final FieldODEState<T> newState;
        if (nextAction == Action.RESET_STATE) {
            newState = handler.resetState(state);
        } else if (nextAction == Action.RESET_DERIVATIVES) {
            newState = state;
        } else {
            newState = null;
        }
        pendingEvent      = false;
        pendingEventTime  = null;

        return newState;

    }

}
