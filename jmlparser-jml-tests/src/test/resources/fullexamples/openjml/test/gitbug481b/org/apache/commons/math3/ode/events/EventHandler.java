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


/** This interface represents a handler for discrete events triggered
 * during ODE integration.
 *
 * <p>Some events can be triggered at discrete times as an ODE problem
 * is solved. This occurs for example when the integration process
 * should be stopped as some state is reached (G-stop facility) when the
 * precise date is unknown a priori, or when the derivatives have
 * discontinuities, or simply when the user wants to monitor some
 * states boundaries crossings.
 * </p>
 *
 * <p>These events are defined as occurring when a <code>g</code>
 * switching function sign changes.</p>
 *
 * <p>Since events are only problem-dependent and are triggered by the
 * independent <i>time</i> variable and the state vector, they can
 * occur at virtually any time, unknown in advance. The integrators will
 * take care to avoid sign changes inside the steps, they will reduce
 * the step size when such an event is detected in order to put this
 * event exactly at the end of the current step. This guarantees that
 * step interpolation (which always has a one step scope) is relevant
 * even in presence of discontinuities. This is independent from the
 * stepsize control provided by integrators that monitor the local
 * error (this event handling feature is available for all integrators,
 * including fixed step ones).</p>
 *
 * @since 1.2
 */

public interface EventHandler  {

    /** Enumerate for actions to be performed when an event occurs. */
    enum Action {

        /** Stop indicator.
         * <p>This value should be used as the return value of the {@link
         * #eventOccurred eventOccurred} method when the integration should be
         * stopped after the event ending the current step.</p>
         */
        STOP,

        /** Reset state indicator.
         * <p>This value should be used as the return value of the {@link
         * #eventOccurred eventOccurred} method when the integration should
         * go on after the event ending the current step, with a new state
         * vector (which will be retrieved thanks to the {@link #resetState
         * resetState} method).</p>
         */
        RESET_STATE,

        /** Reset derivatives indicator.
         * <p>This value should be used as the return value of the {@link
         * #eventOccurred eventOccurred} method when the integration should
         * go on after the event ending the current step, with a new derivatives
         * vector (which will be retrieved thanks to the {@link
         * org.apache.commons.math3.ode.FirstOrderDifferentialEquations#computeDerivatives}
         * method).</p>
         */
        RESET_DERIVATIVES,

        /** Continue indicator.
         * <p>This value should be used as the return value of the {@link
         * #eventOccurred eventOccurred} method when the integration should go
         * on after the event ending the current step.</p>
         */
        CONTINUE;

    }

    /** Initialize event handler at the start of an ODE integration.
     * <p>
     * This method is called once at the start of the integration. It
     * may be used by the event handler to initialize some internal data
     * if needed.
     * </p>
     * @param t0 start value of the independent <i>time</i> variable
     * @param y0 array containing the start value of the state vector
     * @param t target time for the integration
     */
    void init(double t0, double[] y0, double t);

  /** Compute the value of the switching function.

   * <p>The discrete events are generated when the sign of this
   * switching function changes. The integrator will take care to change
   * the stepsize in such a way these events occur exactly at step boundaries.
   * The switching function must be continuous in its roots neighborhood
   * (but not necessarily smooth), as the integrator will need to find its
   * roots to locate precisely the events.</p>
   * <p>Also note that the integrator expect that once an event has occurred,
   * the sign of the switching function at the start of the next step (i.e.
   * just after the event) is the opposite of the sign just before the event.
   * This consistency between the steps <string>must</strong> be preserved,
   * otherwise {@link org.apache.commons.math3.exception.NoBracketingException
   * exceptions} related to root not being bracketed will occur.</p>
   * <p>This need for consistency is sometimes tricky to achieve. A typical
   * example is using an event to model a ball bouncing on the floor. The first
   * idea to represent this would be to have {@code g(t) = h(t)} where h is the
   * height above the floor at time {@code t}. When {@code g(t)} reaches 0, the
   * ball is on the floor, so it should bounce and the typical way to do this is
   * to reverse its vertical velocity. However, this would mean that before the
   * event {@code g(t)} was decreasing from positive values to 0, and after the
   * event {@code g(t)} would be increasing from 0 to positive values again.
   * Consistency is broken here! The solution here is to have {@code g(t) = sign
   * * h(t)}, where sign is a variable with initial value set to {@code +1}. Each
   * time {@link #eventOccurred(double, double[], boolean) eventOccurred} is called,
   * {@code sign} is reset to {@code -sign}. This allows the {@code g(t)}
   * function to remain continuous (and even smooth) even across events, despite
   * {@code h(t)} is not. Basically, the event is used to <em>fold</em> {@code h(t)}
   * at bounce points, and {@code sign} is used to <em>unfold</em> it back, so the
   * solvers sees a {@code g(t)} function which behaves smoothly even across events.</p>

   * @param t current value of the independent <i>time</i> variable
   * @param y array containing the current value of the state vector
   * @return value of the g switching function
   */
  double g(double t, double[] y);

  /** Handle an event and choose what to do next.

   * <p>This method is called when the integrator has accepted a step
   * ending exactly on a sign change of the function, just <em>before</em>
   * the step handler itself is called (see below for scheduling). It
   * allows the user to update his internal data to acknowledge the fact
   * the event has been handled (for example setting a flag in the {@link
   * org.apache.commons.math3.ode.FirstOrderDifferentialEquations
   * differential equations} to switch the derivatives computation in
   * case of discontinuity), or to direct the integrator to either stop
   * or continue integration, possibly with a reset state or derivatives.</p>

   * <ul>
   *   <li>if {@link Action#STOP} is returned, the step handler will be called
   *   with the <code>isLast</code> flag of the {@link
   *   org.apache.commons.math3.ode.sampling.StepHandler#handleStep handleStep}
   *   method set to true and the integration will be stopped,</li>
   *   <li>if {@link Action#RESET_STATE} is returned, the {@link #resetState
   *   resetState} method will be called once the step handler has
   *   finished its task, and the integrator will also recompute the
   *   derivatives,</li>
   *   <li>if {@link Action#RESET_DERIVATIVES} is returned, the integrator
   *   will recompute the derivatives,
   *   <li>if {@link Action#CONTINUE} is returned, no specific action will
   *   be taken (apart from having called this method) and integration
   *   will continue.</li>
   * </ul>

   * <p>The scheduling between this method and the {@link
   * org.apache.commons.math3.ode.sampling.StepHandler StepHandler} method {@link
   * org.apache.commons.math3.ode.sampling.StepHandler#handleStep(
   * org.apache.commons.math3.ode.sampling.StepInterpolator, boolean)
   * handleStep(interpolator, isLast)} is to call this method first and
   * <code>handleStep</code> afterwards. This scheduling allows the integrator to
   * pass <code>true</code> as the <code>isLast</code> parameter to the step
   * handler to make it aware the step will be the last one if this method
   * returns {@link Action#STOP}. As the interpolator may be used to navigate back
   * throughout the last step (as {@link
   * org.apache.commons.math3.ode.sampling.StepNormalizer StepNormalizer}
   * does for example), user code called by this method and user
   * code called by step handlers may experience apparently out of order values
   * of the independent time variable. As an example, if the same user object
   * implements both this {@link EventHandler EventHandler} interface and the
   * {@link org.apache.commons.math3.ode.sampling.FixedStepHandler FixedStepHandler}
   * interface, a <em>forward</em> integration may call its
   * <code>eventOccurred</code> method with t = 10 first and call its
   * <code>handleStep</code> method with t = 9 afterwards. Such out of order
   * calls are limited to the size of the integration step for {@link
   * org.apache.commons.math3.ode.sampling.StepHandler variable step handlers} and
   * to the size of the fixed step for {@link
   * org.apache.commons.math3.ode.sampling.FixedStepHandler fixed step handlers}.</p>

   * @param t current value of the independent <i>time</i> variable
   * @param y array containing the current value of the state vector
   * @param increasing if true, the value of the switching function increases
   * when times increases around event (note that increase is measured with respect
   * to physical time, not with respect to integration which may go backward in time)
   * @return indication of what the integrator should do next, this
   * value must be one of {@link Action#STOP}, {@link Action#RESET_STATE},
   * {@link Action#RESET_DERIVATIVES} or {@link Action#CONTINUE}
   */
  Action eventOccurred(double t, double[] y, boolean increasing);

  /** Reset the state prior to continue the integration.

   * <p>This method is called after the step handler has returned and
   * before the next step is started, but only when {@link
   * #eventOccurred} has itself returned the {@link Action#RESET_STATE}
   * indicator. It allows the user to reset the state vector for the
   * next step, without perturbing the step handler of the finishing
   * step. If the {@link #eventOccurred} never returns the {@link
   * Action#RESET_STATE} indicator, this function will never be called, and it is
   * safe to leave its body empty.</p>

   * @param t current value of the independent <i>time</i> variable
   * @param y array containing the current value of the state vector
   * the new state should be put in the same array
   */
  void resetState(double t, double[] y);

}
