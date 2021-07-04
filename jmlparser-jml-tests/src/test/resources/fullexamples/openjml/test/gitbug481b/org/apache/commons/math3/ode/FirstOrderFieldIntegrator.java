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

import java.util.Collection;

import org.apache.commons.math3.RealFieldElement;
import org.apache.commons.math3.analysis.solvers.BracketedRealFieldUnivariateSolver;
import org.apache.commons.math3.exception.MaxCountExceededException;
import org.apache.commons.math3.exception.NoBracketingException;
import org.apache.commons.math3.exception.NumberIsTooSmallException;
import org.apache.commons.math3.ode.events.FieldEventHandler;
import org.apache.commons.math3.ode.sampling.FieldStepHandler;

/** This interface represents a first order integrator for
 * differential equations.

 * <p>The classes which are devoted to solve first order differential
 * equations should implement this interface. The problems which can
 * be handled should implement the {@link
 * FirstOrderDifferentialEquations} interface.</p>
 *
 * @see FirstOrderFieldDifferentialEquations
 * @param <T> the type of the field elements
 * @since 3.6
 */

public interface FirstOrderFieldIntegrator<T extends RealFieldElement<T>> {

    /** Get the name of the method.
     * @return name of the method
     */
    String getName();

    /** Add a step handler to this integrator.
     * <p>The handler will be called by the integrator for each accepted
     * step.</p>
     * @param handler handler for the accepted steps
     * @see #getStepHandlers()
     * @see #clearStepHandlers()
     */
    void addStepHandler(FieldStepHandler<T> handler);

    /** Get all the step handlers that have been added to the integrator.
     * @return an unmodifiable collection of the added events handlers
     * @see #addStepHandler(FieldStepHandler)
     * @see #clearStepHandlers()
     */
    Collection<FieldStepHandler<T>> getStepHandlers();

    /** Remove all the step handlers that have been added to the integrator.
     * @see #addStepHandler(FieldStepHandler)
     * @see #getStepHandlers()
     */
    void clearStepHandlers();

    /** Add an event handler to the integrator.
     * <p>
     * The default solver is a 5<sup>th</sup> order {@link
     * org.apache.commons.math3.analysis.solvers.FieldBracketingNthOrderBrentSolver}.
     * </p>
     * @param handler event handler
     * @param maxCheckInterval maximal time interval between switching
     * function checks (this interval prevents missing sign changes in
     * case the integration steps becomes very large)
     * @param convergence convergence threshold in the event time search
     * @param maxIterationCount upper limit of the iteration count in
     * the event time search events.
     * @see #addEventHandler(FieldEventHandler, double, double, int,
     * org.apache.commons.math3.analysis.solvers.BracketedRealFieldUnivariateSolver)
     * @see #getEventHandlers()
     * @see #clearEventHandlers()
     */
    void addEventHandler(FieldEventHandler<T>  handler, double maxCheckInterval,
                         double convergence, int maxIterationCount);

    /** Add an event handler to the integrator.
     * @param handler event handler
     * @param maxCheckInterval maximal time interval between switching
     * function checks (this interval prevents missing sign changes in
     * case the integration steps becomes very large)
     * @param convergence convergence threshold in the event time search
     * @param maxIterationCount upper limit of the iteration count in
     * the event time search events.
     * @param solver solver to use to locate the event
     * @see #addEventHandler(FieldEventHandler, double, double, int)
     * @see #getEventHandlers()
     * @see #clearEventHandlers()
     */
    void addEventHandler(FieldEventHandler<T>  handler, double maxCheckInterval,
                         double convergence, int maxIterationCount,
                         BracketedRealFieldUnivariateSolver<T> solver);

    /** Get all the event handlers that have been added to the integrator.
     * @return an unmodifiable collection of the added events handlers
     * @see #addEventHandler(FieldEventHandler, double, double, int)
     * @see #clearEventHandlers()
     */
    Collection<FieldEventHandler<T> > getEventHandlers();

    /** Remove all the event handlers that have been added to the integrator.
     * @see #addEventHandler(FieldEventHandler, double, double, int)
     * @see #getEventHandlers()
     */
    void clearEventHandlers();

    /** Get the current value of the step start time t<sub>i</sub>.
     * <p>This method can be called during integration (typically by
     * the object implementing the {@link FirstOrderDifferentialEquations
     * differential equations} problem) if the value of the current step that
     * is attempted is needed.</p>
     * <p>The result is undefined if the method is called outside of
     * calls to <code>integrate</code>.</p>
     * @return current value of the state at step start time t<sub>i</sub>
     */
    FieldODEStateAndDerivative<T> getCurrentStepStart();

    /** Get the current signed value of the integration stepsize.
     * <p>This method can be called during integration (typically by
     * the object implementing the {@link FirstOrderDifferentialEquations
     * differential equations} problem) if the signed value of the current stepsize
     * that is tried is needed.</p>
     * <p>The result is undefined if the method is called outside of
     * calls to <code>integrate</code>.</p>
     * @return current signed value of the stepsize
     */
    T getCurrentSignedStepsize();

    /** Set the maximal number of differential equations function evaluations.
     * <p>The purpose of this method is to avoid infinite loops which can occur
     * for example when stringent error constraints are set or when lots of
     * discrete events are triggered, thus leading to many rejected steps.</p>
     * @param maxEvaluations maximal number of function evaluations (negative
     * values are silently converted to maximal integer value, thus representing
     * almost unlimited evaluations)
     */
    void setMaxEvaluations(int maxEvaluations);

    /** Get the maximal number of functions evaluations.
     * @return maximal number of functions evaluations
     */
    int getMaxEvaluations();

    /** Get the number of evaluations of the differential equations function.
     * <p>
     * The number of evaluations corresponds to the last call to the
     * <code>integrate</code> method. It is 0 if the method has not been called yet.
     * </p>
     * @return number of evaluations of the differential equations function
     */
    int getEvaluations();

    /** Integrate the differential equations up to the given time.
     * <p>This method solves an Initial Value Problem (IVP).</p>
     * <p>Since this method stores some internal state variables made
     * available in its public interface during integration ({@link
     * #getCurrentSignedStepsize()}), it is <em>not</em> thread-safe.</p>
     * @param equations differential equations to integrate
     * @param initialState initial state (time, primary and secondary state vectors)
     * @param finalTime target time for the integration
     * (can be set to a value smaller than {@code t0} for backward integration)
     * @return final state, its time will be the same as {@code finalTime} if
     * integration reached its target, but may be different if some {@link
     * org.apache.commons.math3.ode.events.FieldEventHandler} stops it at some point.
     * @exception NumberIsTooSmallException if integration step is too small
     * @exception MaxCountExceededException if the number of functions evaluations is exceeded
     * @exception NoBracketingException if the location of an event cannot be bracketed
     */
    FieldODEStateAndDerivative<T> integrate(FieldExpandableODE<T> equations,
                                            FieldODEState<T> initialState, T finalTime)
        throws NumberIsTooSmallException, MaxCountExceededException, NoBracketingException;

}
