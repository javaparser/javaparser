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

import java.io.Externalizable;

import org.apache.commons.math3.exception.MaxCountExceededException;

/** This interface represents an interpolator over the last step
 * during an ODE integration.
 *
 * <p>The various ODE integrators provide objects implementing this
 * interface to the step handlers. These objects are often custom
 * objects tightly bound to the integrator internal algorithms. The
 * handlers can use these objects to retrieve the state vector at
 * intermediate times between the previous and the current grid points
 * (this feature is often called dense output).</p>
 * <p>One important thing to note is that the step handlers may be so
 * tightly bound to the integrators that they often share some internal
 * state arrays. This imply that one should <em>never</em> use a direct
 * reference to a step interpolator outside of the step handler, either
 * for future use or for use in another thread. If such a need arise, the
 * step interpolator <em>must</em> be copied using the dedicated
 * {@link #copy()} method.
 * </p>
 *
 * @see org.apache.commons.math3.ode.FirstOrderIntegrator
 * @see org.apache.commons.math3.ode.SecondOrderIntegrator
 * @see StepHandler
 * @since 1.2
 */

public interface StepInterpolator extends Externalizable {

  /**
   * Get the previous grid point time.
   * @return previous grid point time
   */
  double getPreviousTime();

  /**
   * Get the current grid point time.
   * @return current grid point time
   */
  double getCurrentTime();

  /**
   * Get the time of the interpolated point.
   * If {@link #setInterpolatedTime} has not been called, it returns
   * the current grid point time.
   * @return interpolation point time
   */
  double getInterpolatedTime();

  /**
   * Set the time of the interpolated point.
   * <p>Setting the time outside of the current step is now allowed, but
   * should be used with care since the accuracy of the interpolator will
   * probably be very poor far from this step. This allowance has been
   * added to simplify implementation of search algorithms near the
   * step endpoints.</p>
   * <p>Setting the time changes the instance internal state. This includes
   * the internal arrays returned in {@link #getInterpolatedState()},
   * {@link #getInterpolatedDerivatives()}, {@link
   * #getInterpolatedSecondaryState(int)} and {@link
   * #getInterpolatedSecondaryDerivatives(int)}. So if their content must be preserved
   * across several calls, user must copy them.</p>
   * @param time time of the interpolated point
   * @see #getInterpolatedState()
   * @see #getInterpolatedDerivatives()
   * @see #getInterpolatedSecondaryState(int)
   * @see #getInterpolatedSecondaryDerivatives(int)
   */
  void setInterpolatedTime(double time);

  /**
   * Get the state vector of the interpolated point.
   * <p>The returned vector is a reference to a reused array, so
   * it should not be modified and it should be copied if it needs
   * to be preserved across several calls to the associated
   * {@link #setInterpolatedTime(double)} method.</p>
   * @return state vector at time {@link #getInterpolatedTime}
   * @see #getInterpolatedDerivatives()
   * @see #getInterpolatedSecondaryState(int)
   * @see #getInterpolatedSecondaryDerivatives(int)
   * @see #setInterpolatedTime(double)
   * @exception MaxCountExceededException if the number of functions evaluations is exceeded
   */
  double[] getInterpolatedState() throws MaxCountExceededException;

  /**
   * Get the derivatives of the state vector of the interpolated point.
   * <p>The returned vector is a reference to a reused array, so
   * it should not be modified and it should be copied if it needs
   * to be preserved across several calls to the associated
   * {@link #setInterpolatedTime(double)} method.</p>
   * @return derivatives of the state vector at time {@link #getInterpolatedTime}
   * @see #getInterpolatedState()
   * @see #getInterpolatedSecondaryState(int)
   * @see #getInterpolatedSecondaryDerivatives(int)
   * @see #setInterpolatedTime(double)
   * @since 2.0
   * @exception MaxCountExceededException if the number of functions evaluations is exceeded
   */
  double[] getInterpolatedDerivatives() throws MaxCountExceededException;

  /** Get the interpolated secondary state corresponding to the secondary equations.
   * <p>The returned vector is a reference to a reused array, so
   * it should not be modified and it should be copied if it needs
   * to be preserved across several calls to the associated
   * {@link #setInterpolatedTime(double)} method.</p>
   * @param index index of the secondary set, as returned by {@link
   * org.apache.commons.math3.ode.ExpandableStatefulODE#addSecondaryEquations(
   * org.apache.commons.math3.ode.SecondaryEquations)
   * ExpandableStatefulODE.addSecondaryEquations(SecondaryEquations)}
   * @return interpolated secondary state at the current interpolation date
   * @see #getInterpolatedState()
   * @see #getInterpolatedDerivatives()
   * @see #getInterpolatedSecondaryDerivatives(int)
   * @see #setInterpolatedTime(double)
   * @since 3.0
   * @exception MaxCountExceededException if the number of functions evaluations is exceeded
   */
  double[] getInterpolatedSecondaryState(int index) throws MaxCountExceededException;

  /** Get the interpolated secondary derivatives corresponding to the secondary equations.
   * <p>The returned vector is a reference to a reused array, so
   * it should not be modified and it should be copied if it needs
   * to be preserved across several calls.</p>
   * @param index index of the secondary set, as returned by {@link
   * org.apache.commons.math3.ode.ExpandableStatefulODE#addSecondaryEquations(
   * org.apache.commons.math3.ode.SecondaryEquations)
   * ExpandableStatefulODE.addSecondaryEquations(SecondaryEquations)}
   * @return interpolated secondary derivatives at the current interpolation date
   * @see #getInterpolatedState()
   * @see #getInterpolatedDerivatives()
   * @see #getInterpolatedSecondaryState(int)
   * @see #setInterpolatedTime(double)
   * @since 3.0
   * @exception MaxCountExceededException if the number of functions evaluations is exceeded
   */
  double[] getInterpolatedSecondaryDerivatives(int index) throws MaxCountExceededException;

  /** Check if the natural integration direction is forward.
   * <p>This method provides the integration direction as specified by
   * the integrator itself, it avoid some nasty problems in
   * degenerated cases like null steps due to cancellation at step
   * initialization, step control or discrete events
   * triggering.</p>
   * @return true if the integration variable (time) increases during
   * integration
   */
  boolean isForward();

  /** Copy the instance.
   * <p>The copied instance is guaranteed to be independent from the
   * original one. Both can be used with different settings for
   * interpolated time without any side effect.</p>
   * @return a deep copy of the instance, which can be used independently.
   * @see #setInterpolatedTime(double)
   * @exception MaxCountExceededException if the number of functions evaluations is exceeded
   * during step finalization
   */
   StepInterpolator copy() throws MaxCountExceededException;

}
