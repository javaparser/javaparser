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

import org.apache.commons.math3.analysis.solvers.BracketingNthOrderBrentSolver;
import org.apache.commons.math3.analysis.solvers.UnivariateSolver;
import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.MaxCountExceededException;
import org.apache.commons.math3.exception.NoBracketingException;
import org.apache.commons.math3.exception.NumberIsTooSmallException;
import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.ode.events.EventHandler;
import org.apache.commons.math3.ode.events.EventState;
import org.apache.commons.math3.ode.sampling.AbstractStepInterpolator;
import org.apache.commons.math3.ode.sampling.StepHandler;
import org.apache.commons.math3.util.FastMath;
import org.apache.commons.math3.util.IntegerSequence;
import org.apache.commons.math3.util.Precision;

/**
 * Base class managing common boilerplate for all integrators.
 * @since 2.0
 */
public abstract class AbstractIntegrator implements FirstOrderIntegrator {

    /** Step handler. */
    protected Collection<StepHandler> stepHandlers;

    /** Current step start time. */
    protected double stepStart;

    /** Current stepsize. */
    protected double stepSize;

    /** Indicator for last step. */
    protected boolean isLastStep;

    /** Indicator that a state or derivative reset was triggered by some event. */
    protected boolean resetOccurred;

    /** Events states. */
    private Collection<EventState> eventsStates;

    /** Initialization indicator of events states. */
    private boolean statesInitialized;

    /** Name of the method. */
    private final String name;

    /** Counter for number of evaluations. */
    private IntegerSequence.Incrementor evaluations;

    /** Differential equations to integrate. */
    private transient ExpandableStatefulODE expandable;

    /** Build an instance.
     * @param name name of the method
     */
    public AbstractIntegrator(final String name) {
        this.name = name;
        stepHandlers = new ArrayList<StepHandler>();
        stepStart = Double.NaN;
        stepSize  = Double.NaN;
        eventsStates = new ArrayList<EventState>();
        statesInitialized = false;
        evaluations = IntegerSequence.Incrementor.create().withMaximalCount(Integer.MAX_VALUE);
    }

    /** Build an instance with a null name.
     */
    protected AbstractIntegrator() {
        this(null);
    }

    /** {@inheritDoc} */
    public String getName() {
        return name;
    }

    /** {@inheritDoc} */
    public void addStepHandler(final StepHandler handler) {
        stepHandlers.add(handler);
    }

    /** {@inheritDoc} */
    public Collection<StepHandler> getStepHandlers() {
        return Collections.unmodifiableCollection(stepHandlers);
    }

    /** {@inheritDoc} */
    public void clearStepHandlers() {
        stepHandlers.clear();
    }

    /** {@inheritDoc} */
    public void addEventHandler(final EventHandler handler,
                                final double maxCheckInterval,
                                final double convergence,
                                final int maxIterationCount) {
        addEventHandler(handler, maxCheckInterval, convergence,
                        maxIterationCount,
                        new BracketingNthOrderBrentSolver(convergence, 5));
    }

    /** {@inheritDoc} */
    public void addEventHandler(final EventHandler handler,
                                final double maxCheckInterval,
                                final double convergence,
                                final int maxIterationCount,
                                final UnivariateSolver solver) {
        eventsStates.add(new EventState(handler, maxCheckInterval, convergence,
                                        maxIterationCount, solver));
    }

    /** {@inheritDoc} */
    public Collection<EventHandler> getEventHandlers() {
        final List<EventHandler> list = new ArrayList<EventHandler>(eventsStates.size());
        for (EventState state : eventsStates) {
            list.add(state.getEventHandler());
        }
        return Collections.unmodifiableCollection(list);
    }

    /** {@inheritDoc} */
    public void clearEventHandlers() {
        eventsStates.clear();
    }

    /** {@inheritDoc} */
    public double getCurrentStepStart() {
        return stepStart;
    }

    /** {@inheritDoc} */
    public double getCurrentSignedStepsize() {
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
     * @param t0 start value of the independent <i>time</i> variable
     * @param y0 array containing the start value of the state vector
     * @param t target time for the integration
     */
    protected void initIntegration(final double t0, final double[] y0, final double t) {

        evaluations = evaluations.withStart(0);

        for (final EventState state : eventsStates) {
            state.setExpandable(expandable);
            state.getEventHandler().init(t0, y0, t);
        }

        for (StepHandler handler : stepHandlers) {
            handler.init(t0, y0, t);
        }

        setStateInitialized(false);

    }

    /** Set the equations.
     * @param equations equations to set
     */
    protected void setEquations(final ExpandableStatefulODE equations) {
        this.expandable = equations;
    }

    /** Get the differential equations to integrate.
     * @return differential equations to integrate
     * @since 3.2
     */
    protected ExpandableStatefulODE getExpandable() {
        return expandable;
    }

    /** Get the evaluations counter.
     * @return evaluations counter
     * @since 3.2
     * @deprecated as of 3.6 replaced with {@link #getCounter()}
     */
    @Deprecated
    protected org.apache.commons.math3.util.Incrementor getEvaluationsCounter() {
        return org.apache.commons.math3.util.Incrementor.wrap(evaluations);
    }

    /** Get the evaluations counter.
     * @return evaluations counter
     * @since 3.6
     */
    protected IntegerSequence.Incrementor getCounter() {
        return evaluations;
    }

    /** {@inheritDoc} */
    public double integrate(final FirstOrderDifferentialEquations equations,
                            final double t0, final double[] y0, final double t, final double[] y)
        throws DimensionMismatchException, NumberIsTooSmallException,
               MaxCountExceededException, NoBracketingException {

        if (y0.length != equations.getDimension()) {
            throw new DimensionMismatchException(y0.length, equations.getDimension());
        }
        if (y.length != equations.getDimension()) {
            throw new DimensionMismatchException(y.length, equations.getDimension());
        }

        // prepare expandable stateful equations
        final ExpandableStatefulODE expandableODE = new ExpandableStatefulODE(equations);
        expandableODE.setTime(t0);
        expandableODE.setPrimaryState(y0);

        // perform integration
        integrate(expandableODE, t);

        // extract results back from the stateful equations
        System.arraycopy(expandableODE.getPrimaryState(), 0, y, 0, y.length);
        return expandableODE.getTime();

    }

    /** Integrate a set of differential equations up to the given time.
     * <p>This method solves an Initial Value Problem (IVP).</p>
     * <p>The set of differential equations is composed of a main set, which
     * can be extended by some sets of secondary equations. The set of
     * equations must be already set up with initial time and partial states.
     * At integration completion, the final time and partial states will be
     * available in the same object.</p>
     * <p>Since this method stores some internal state variables made
     * available in its public interface during integration ({@link
     * #getCurrentSignedStepsize()}), it is <em>not</em> thread-safe.</p>
     * @param equations complete set of differential equations to integrate
     * @param t target time for the integration
     * (can be set to a value smaller than <code>t0</code> for backward integration)
     * @exception NumberIsTooSmallException if integration step is too small
     * @throws DimensionMismatchException if the dimension of the complete state does not
     * match the complete equations sets dimension
     * @exception MaxCountExceededException if the number of functions evaluations is exceeded
     * @exception NoBracketingException if the location of an event cannot be bracketed
     */
    public abstract void integrate(ExpandableStatefulODE equations, double t)
        throws NumberIsTooSmallException, DimensionMismatchException,
               MaxCountExceededException, NoBracketingException;

    /** Compute the derivatives and check the number of evaluations.
     * @param t current value of the independent <I>time</I> variable
     * @param y array containing the current value of the state vector
     * @param yDot placeholder array where to put the time derivative of the state vector
     * @exception MaxCountExceededException if the number of functions evaluations is exceeded
     * @exception DimensionMismatchException if arrays dimensions do not match equations settings
     * @exception NullPointerException if the ODE equations have not been set (i.e. if this method
     * is called outside of a call to {@link #integrate(ExpandableStatefulODE, double)} or {@link
     * #integrate(FirstOrderDifferentialEquations, double, double[], double, double[])})
     */
    public void computeDerivatives(final double t, final double[] y, final double[] yDot)
        throws MaxCountExceededException, DimensionMismatchException, NullPointerException {
        evaluations.increment();
        expandable.computeDerivatives(t, y, yDot);
    }

    /** Set the stateInitialized flag.
     * <p>This method must be called by integrators with the value
     * {@code false} before they start integration, so a proper lazy
     * initialization is done automatically on the first step.</p>
     * @param stateInitialized new value for the flag
     * @since 2.2
     */
    protected void setStateInitialized(final boolean stateInitialized) {
        this.statesInitialized = stateInitialized;
    }

    /** Accept a step, triggering events and step handlers.
     * @param interpolator step interpolator
     * @param y state vector at step end time, must be reset if an event
     * asks for resetting or if an events stops integration during the step
     * @param yDot placeholder array where to put the time derivative of the state vector
     * @param tEnd final integration time
     * @return time at end of step
     * @exception MaxCountExceededException if the interpolator throws one because
     * the number of functions evaluations is exceeded
     * @exception NoBracketingException if the location of an event cannot be bracketed
     * @exception DimensionMismatchException if arrays dimensions do not match equations settings
     * @since 2.2
     */
    protected double acceptStep(final AbstractStepInterpolator interpolator,
                                final double[] y, final double[] yDot, final double tEnd)
        throws MaxCountExceededException, DimensionMismatchException, NoBracketingException {

            double previousT = interpolator.getGlobalPreviousTime();
            final double currentT = interpolator.getGlobalCurrentTime();

            // initialize the events states if needed
            if (! statesInitialized) {
                for (EventState state : eventsStates) {
                    state.reinitializeBegin(interpolator);
                }
                statesInitialized = true;
            }

            // search for next events that may occur during the step
            final int orderingSign = interpolator.isForward() ? +1 : -1;
            SortedSet<EventState> occurringEvents = new TreeSet<EventState>(new Comparator<EventState>() {

                /** {@inheritDoc} */
                public int compare(EventState es0, EventState es1) {
                    return orderingSign * Double.compare(es0.getEventTime(), es1.getEventTime());
                }

            });

            for (final EventState state : eventsStates) {
                if (state.evaluateStep(interpolator)) {
                    // the event occurs during the current step
                    occurringEvents.add(state);
                }
            }

            while (!occurringEvents.isEmpty()) {

                // handle the chronologically first event
                final Iterator<EventState> iterator = occurringEvents.iterator();
                final EventState currentEvent = iterator.next();
                iterator.remove();

                // restrict the interpolator to the first part of the step, up to the event
                final double eventT = currentEvent.getEventTime();
                interpolator.setSoftPreviousTime(previousT);
                interpolator.setSoftCurrentTime(eventT);

                // get state at event time
                interpolator.setInterpolatedTime(eventT);
                final double[] eventYComplete = new double[y.length];
                expandable.getPrimaryMapper().insertEquationData(interpolator.getInterpolatedState(),
                                                                 eventYComplete);
                int index = 0;
                for (EquationsMapper secondary : expandable.getSecondaryMappers()) {
                    secondary.insertEquationData(interpolator.getInterpolatedSecondaryState(index++),
                                                 eventYComplete);
                }

                // advance all event states to current time
                for (final EventState state : eventsStates) {
                    state.stepAccepted(eventT, eventYComplete);
                    isLastStep = isLastStep || state.stop();
                }

                // handle the first part of the step, up to the event
                for (final StepHandler handler : stepHandlers) {
                    handler.handleStep(interpolator, isLastStep);
                }

                if (isLastStep) {
                    // the event asked to stop integration
                    System.arraycopy(eventYComplete, 0, y, 0, y.length);
                    return eventT;
                }

                boolean needReset = false;
                resetOccurred = false;
                needReset = currentEvent.reset(eventT, eventYComplete);
                if (needReset) {
                    // some event handler has triggered changes that
                    // invalidate the derivatives, we need to recompute them
                    interpolator.setInterpolatedTime(eventT);
                    System.arraycopy(eventYComplete, 0, y, 0, y.length);
                    computeDerivatives(eventT, y, yDot);
                    resetOccurred = true;
                    return eventT;
                }

                // prepare handling of the remaining part of the step
                previousT = eventT;
                interpolator.setSoftPreviousTime(eventT);
                interpolator.setSoftCurrentTime(currentT);

                // check if the same event occurs again in the remaining part of the step
                if (currentEvent.evaluateStep(interpolator)) {
                    // the event occurs during the current step
                    occurringEvents.add(currentEvent);
                }

            }

            // last part of the step, after the last event
            interpolator.setInterpolatedTime(currentT);
            final double[] currentY = new double[y.length];
            expandable.getPrimaryMapper().insertEquationData(interpolator.getInterpolatedState(),
                                                             currentY);
            int index = 0;
            for (EquationsMapper secondary : expandable.getSecondaryMappers()) {
                secondary.insertEquationData(interpolator.getInterpolatedSecondaryState(index++),
                                             currentY);
            }
            for (final EventState state : eventsStates) {
                state.stepAccepted(currentT, currentY);
                isLastStep = isLastStep || state.stop();
            }
            isLastStep = isLastStep || Precision.equals(currentT, tEnd, 1);

            // handle the remaining part of the step, after all events if any
            for (StepHandler handler : stepHandlers) {
                handler.handleStep(interpolator, isLastStep);
            }

            return currentT;

    }

    /** Check the integration span.
     * @param equations set of differential equations
     * @param t target time for the integration
     * @exception NumberIsTooSmallException if integration span is too small
     * @exception DimensionMismatchException if adaptive step size integrators
     * tolerance arrays dimensions are not compatible with equations settings
     */
    protected void sanityChecks(final ExpandableStatefulODE equations, final double t)
        throws NumberIsTooSmallException, DimensionMismatchException {

        final double threshold = 1000 * FastMath.ulp(FastMath.max(FastMath.abs(equations.getTime()),
                                                                  FastMath.abs(t)));
        final double dt = FastMath.abs(equations.getTime() - t);
        if (dt <= threshold) {
            throw new NumberIsTooSmallException(LocalizedFormats.TOO_SMALL_INTEGRATION_INTERVAL,
                                                dt, threshold, false);
        }

    }

}
