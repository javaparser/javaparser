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

package org.apache.commons.math3.ode;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Iterator;
import java.util.List;
import java.util.SortedSet;
import java.util.TreeSet;

import org.apache.commons.math3.Field;
import org.apache.commons.math3.RealFieldElement;
import org.apache.commons.math3.analysis.solvers.BracketedRealFieldUnivariateSolver;
import org.apache.commons.math3.analysis.solvers.FieldBracketingNthOrderBrentSolver;
import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.MaxCountExceededException;
import org.apache.commons.math3.exception.NoBracketingException;
import org.apache.commons.math3.exception.NumberIsTooSmallException;
import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.ode.events.FieldEventHandler;
import org.apache.commons.math3.ode.events.FieldEventState;
import org.apache.commons.math3.ode.sampling.AbstractFieldStepInterpolator;
import org.apache.commons.math3.ode.sampling.FieldStepHandler;
import org.apache.commons.math3.util.FastMath;
import org.apache.commons.math3.util.IntegerSequence;

/**
 * Base class managing common boilerplate for all integrators.
 * @param <T> the type of the field elements
 * @since 3.6
 */
public abstract class AbstractFieldIntegrator<T extends RealFieldElement<T>> implements FirstOrderFieldIntegrator<T> {

    /** Default relative accuracy. */
    private static final double DEFAULT_RELATIVE_ACCURACY = 1e-14;

    /** Default function value accuracy. */
    private static final double DEFAULT_FUNCTION_VALUE_ACCURACY = 1e-15;

    /** Step handler. */
    private Collection<FieldStepHandler<T>> stepHandlers;

    /** Current step start. */
    private FieldODEStateAndDerivative<T> stepStart;

    /** Current stepsize. */
    private T stepSize;

    /** Indicator for last step. */
    private boolean isLastStep;

    /** Indicator that a state or derivative reset was triggered by some event. */
    private boolean resetOccurred;

    /** Field to which the time and state vector elements belong. */
    private final Field<T> field;

    /** Events states. */
    private Collection<FieldEventState<T>> eventsStates;

    /** Initialization indicator of events states. */
    private boolean statesInitialized;

    /** Name of the method. */
    private final String name;

    /** Counter for number of evaluations. */
    private IntegerSequence.Incrementor evaluations;

    /** Differential equations to integrate. */
    private transient FieldExpandableODE<T> equations;

    /** Build an instance.
     * @param field field to which the time and state vector elements belong
     * @param name name of the method
     */
    protected AbstractFieldIntegrator(final Field<T> field, final String name) {
        this.field        = field;
        this.name         = name;
        stepHandlers      = new ArrayList<FieldStepHandler<T>>();
        stepStart         = null;
        stepSize          = null;
        eventsStates      = new ArrayList<FieldEventState<T>>();
        statesInitialized = false;
        evaluations       = IntegerSequence.Incrementor.create().withMaximalCount(Integer.MAX_VALUE);
    }

    /** Get the field to which state vector elements belong.
     * @return field to which state vector elements belong
     */
    public Field<T> getField() {
        return field;
    }

    /** {@inheritDoc} */
    public String getName() {
        return name;
    }

    /** {@inheritDoc} */
    public void addStepHandler(final FieldStepHandler<T> handler) {
        stepHandlers.add(handler);
    }

    /** {@inheritDoc} */
    public Collection<FieldStepHandler<T>> getStepHandlers() {
        return Collections.unmodifiableCollection(stepHandlers);
    }

    /** {@inheritDoc} */
    public void clearStepHandlers() {
        stepHandlers.clear();
    }

    /** {@inheritDoc} */
    public void addEventHandler(final FieldEventHandler<T> handler,
                                final double maxCheckInterval,
                                final double convergence,
                                final int maxIterationCount) {
        addEventHandler(handler, maxCheckInterval, convergence,
                        maxIterationCount,
                        new FieldBracketingNthOrderBrentSolver<T>(field.getZero().add(DEFAULT_RELATIVE_ACCURACY),
                                                                  field.getZero().add(convergence),
                                                                  field.getZero().add(DEFAULT_FUNCTION_VALUE_ACCURACY),
                                                                  5));
    }

    /** {@inheritDoc} */
    public void addEventHandler(final FieldEventHandler<T> handler,
                                final double maxCheckInterval,
                                final double convergence,
                                final int maxIterationCount,
                                final BracketedRealFieldUnivariateSolver<T> solver) {
        eventsStates.add(new FieldEventState<T>(handler, maxCheckInterval, field.getZero().add(convergence),
                                                maxIterationCount, solver));
    }

    /** {@inheritDoc} */
    public Collection<FieldEventHandler<T>> getEventHandlers() {
        final List<FieldEventHandler<T>> list = new ArrayList<FieldEventHandler<T>>(eventsStates.size());
        for (FieldEventState<T> state : eventsStates) {
            list.add(state.getEventHandler());
        }
        return Collections.unmodifiableCollection(list);
    }

    /** {@inheritDoc} */
    public void clearEventHandlers() {
        eventsStates.clear();
    }

    /** {@inheritDoc} */
    public FieldODEStateAndDerivative<T> getCurrentStepStart() {
        return stepStart;
    }

    /** {@inheritDoc} */
    public T getCurrentSignedStepsize() {
        return stepSize;
    }

    /** {@inheritDoc} */
    public void setMaxEvaluations(int maxEvaluations) {
        evaluations = evaluations.withMaximalCount((maxEvaluations < 0) ? Integer.MAX_VALUE : maxEvaluations);
    }

    /** {@inheritDoc} */
    public int getMaxEvaluations() {
        return evaluations.getMaximalCount();
    }

    /** {@inheritDoc} */
    public int getEvaluations() {
        return evaluations.getCount();
    }

    /** Prepare the start of an integration.
     * @param eqn equations to integrate
     * @param t0 start value of the independent <i>time</i> variable
     * @param y0 array containing the start value of the state vector
     * @param t target time for the integration
     * @return initial state with derivatives added
     */
    protected FieldODEStateAndDerivative<T> initIntegration(final FieldExpandableODE<T> eqn,
                                                            final T t0, final T[] y0, final T t) {

        this.equations = eqn;
        evaluations    = evaluations.withStart(0);

        // initialize ODE
        eqn.init(t0, y0, t);

        // set up derivatives of initial state
        final T[] y0Dot = computeDerivatives(t0, y0);
        final FieldODEStateAndDerivative<T> state0 = new FieldODEStateAndDerivative<T>(t0, y0, y0Dot);

        // initialize event handlers
        for (final FieldEventState<T> state : eventsStates) {
            state.getEventHandler().init(state0, t);
        }

        // initialize step handlers
        for (FieldStepHandler<T> handler : stepHandlers) {
            handler.init(state0, t);
        }

        setStateInitialized(false);

        return state0;

    }

    /** Get the differential equations to integrate.
     * @return differential equations to integrate
     */
    protected FieldExpandableODE<T> getEquations() {
        return equations;
    }

    /** Get the evaluations counter.
     * @return evaluations counter
     */
    protected IntegerSequence.Incrementor getEvaluationsCounter() {
        return evaluations;
    }

    /** Compute the derivatives and check the number of evaluations.
     * @param t current value of the independent <I>time</I> variable
     * @param y array containing the current value of the state vector
     * @return state completed with derivatives
     * @exception DimensionMismatchException if arrays dimensions do not match equations settings
     * @exception MaxCountExceededException if the number of functions evaluations is exceeded
     * @exception NullPointerException if the ODE equations have not been set (i.e. if this method
     * is called outside of a call to {@link #integrate(FieldExpandableODE, FieldODEState,
     * RealFieldElement) integrate}
     */
    public T[] computeDerivatives(final T t, final T[] y)
        throws DimensionMismatchException, MaxCountExceededException, NullPointerException {
        evaluations.increment();
        return equations.computeDerivatives(t, y);
    }

    /** Set the stateInitialized flag.
     * <p>This method must be called by integrators with the value
     * {@code false} before they start integration, so a proper lazy
     * initialization is done automatically on the first step.</p>
     * @param stateInitialized new value for the flag
     */
    protected void setStateInitialized(final boolean stateInitialized) {
        this.statesInitialized = stateInitialized;
    }

    /** Accept a step, triggering events and step handlers.
     * @param interpolator step interpolator
     * @param tEnd final integration time
     * @return state at end of step
     * @exception MaxCountExceededException if the interpolator throws one because
     * the number of functions evaluations is exceeded
     * @exception NoBracketingException if the location of an event cannot be bracketed
     * @exception DimensionMismatchException if arrays dimensions do not match equations settings
     */
    protected FieldODEStateAndDerivative<T> acceptStep(final AbstractFieldStepInterpolator<T> interpolator,
                                                       final T tEnd)
        throws MaxCountExceededException, DimensionMismatchException, NoBracketingException {

            FieldODEStateAndDerivative<T> previousState = interpolator.getGlobalPreviousState();
            final FieldODEStateAndDerivative<T> currentState = interpolator.getGlobalCurrentState();

            // initialize the events states if needed
            if (! statesInitialized) {
                for (FieldEventState<T> state : eventsStates) {
                    state.reinitializeBegin(interpolator);
                }
                statesInitialized = true;
            }

            // search for next events that may occur during the step
            final int orderingSign = interpolator.isForward() ? +1 : -1;
            SortedSet<FieldEventState<T>> occurringEvents = new TreeSet<FieldEventState<T>>(new Comparator<FieldEventState<T>>() {

                /** {@inheritDoc} */
                public int compare(FieldEventState<T> es0, FieldEventState<T> es1) {
                    return orderingSign * Double.compare(es0.getEventTime().getReal(), es1.getEventTime().getReal());
                }

            });

            for (final FieldEventState<T> state : eventsStates) {
                if (state.evaluateStep(interpolator)) {
                    // the event occurs during the current step
                    occurringEvents.add(state);
                }
            }

            AbstractFieldStepInterpolator<T> restricted = interpolator;
            while (!occurringEvents.isEmpty()) {

                // handle the chronologically first event
                final Iterator<FieldEventState<T>> iterator = occurringEvents.iterator();
                final FieldEventState<T> currentEvent = iterator.next();
                iterator.remove();

                // get state at event time
                final FieldODEStateAndDerivative<T> eventState = restricted.getInterpolatedState(currentEvent.getEventTime());

                // restrict the interpolator to the first part of the step, up to the event
                restricted = restricted.restrictStep(previousState, eventState);

                // advance all event states to current time
                for (final FieldEventState<T> state : eventsStates) {
                    state.stepAccepted(eventState);
                    isLastStep = isLastStep || state.stop();
                }

                // handle the first part of the step, up to the event
                for (final FieldStepHandler<T> handler : stepHandlers) {
                    handler.handleStep(restricted, isLastStep);
                }

                if (isLastStep) {
                    // the event asked to stop integration
                    return eventState;
                }

                FieldODEState<T> newState = null;
                resetOccurred = false;
                for (final FieldEventState<T> state : eventsStates) {
                    newState = state.reset(eventState);
                    if (newState != null) {
                        // some event handler has triggered changes that
                        // invalidate the derivatives, we need to recompute them
                        final T[] y    = equations.getMapper().mapState(newState);
                        final T[] yDot = computeDerivatives(newState.getTime(), y);
                        resetOccurred = true;
                        return equations.getMapper().mapStateAndDerivative(newState.getTime(), y, yDot);
                    }
                }

                // prepare handling of the remaining part of the step
                previousState = eventState;
                restricted = restricted.restrictStep(eventState, currentState);

                // check if the same event occurs again in the remaining part of the step
                if (currentEvent.evaluateStep(restricted)) {
                    // the event occurs during the current step
                    occurringEvents.add(currentEvent);
                }

            }

            // last part of the step, after the last event
            for (final FieldEventState<T> state : eventsStates) {
                state.stepAccepted(currentState);
                isLastStep = isLastStep || state.stop();
            }
            isLastStep = isLastStep || currentState.getTime().subtract(tEnd).abs().getReal() <= FastMath.ulp(tEnd.getReal());

            // handle the remaining part of the step, after all events if any
            for (FieldStepHandler<T> handler : stepHandlers) {
                handler.handleStep(restricted, isLastStep);
            }

            return currentState;

    }

    /** Check the integration span.
     * @param eqn set of differential equations
     * @param t target time for the integration
     * @exception NumberIsTooSmallException if integration span is too small
     * @exception DimensionMismatchException if adaptive step size integrators
     * tolerance arrays dimensions are not compatible with equations settings
     */
    protected void sanityChecks(final FieldODEState<T> eqn, final T t)
        throws NumberIsTooSmallException, DimensionMismatchException {

        final double threshold = 1000 * FastMath.ulp(FastMath.max(FastMath.abs(eqn.getTime().getReal()),
                                                                  FastMath.abs(t.getReal())));
        final double dt = eqn.getTime().subtract(t).abs().getReal();
        if (dt <= threshold) {
            throw new NumberIsTooSmallException(LocalizedFormats.TOO_SMALL_INTEGRATION_INTERVAL,
                                                dt, threshold, false);
        }

    }

    /** Check if a reset occurred while last step was accepted.
     * @return true if a reset occurred while last step was accepted
     */
    protected boolean resetOccurred() {
        return resetOccurred;
    }

    /** Set the current step size.
     * @param stepSize step size to set
     */
    protected void setStepSize(final T stepSize) {
        this.stepSize = stepSize;
    }

    /** Get the current step size.
     * @return current step size
     */
    protected T getStepSize() {
        return stepSize;
    }
    /** Set current step start.
     * @param stepStart step start
     */
    protected void setStepStart(final FieldODEStateAndDerivative<T> stepStart) {
        this.stepStart = stepStart;
    }

    /** Getcurrent step start.
     * @return current step start
     */
    protected FieldODEStateAndDerivative<T> getStepStart() {
        return stepStart;
    }

    /** Set the last state flag.
     * @param isLastStep if true, this step is the last one
     */
    protected void setIsLastStep(final boolean isLastStep) {
        this.isLastStep = isLastStep;
    }

    /** Check if this step is the last one.
     * @return true if this step is the last one
     */
    protected boolean isLastStep() {
        return isLastStep;
    }

}
