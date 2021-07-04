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
import org.apache.commons.math3.ode.FieldODEStateAndDerivative;

/** This interface represents an interpolator over the last step
 * during an ODE integration.
 *
 * <p>The various ODE integrators provide objects implementing this
 * interface to the step handlers. These objects are often custom
 * objects tightly bound to the integrator internal algorithms. The
 * handlers can use these objects to retrieve the state vector at
 * intermediate times between the previous and the current grid points
 * (this feature is often called dense output).</p>
 *
 * @param <T> the type of the field elements
 * @see org.apache.commons.math3.ode.FirstOrderFieldIntegrator
 * @see FieldStepHandler
 * @since 3.6
 */

public interface FieldStepInterpolator<T extends RealFieldElement<T>> {

  /**
   * Get the state at previous grid point time.
   * @return state at previous grid point time
   */
  FieldODEStateAndDerivative<T> getPreviousState();

  /**
   * Get the state at current grid point time.
   * @return state at current grid point time
   */
  FieldODEStateAndDerivative<T> getCurrentState();

  /**
   * Get the state at interpolated time.
   * <p>Setting the time outside of the current step is allowed, but
   * should be used with care since the accuracy of the interpolator will
   * probably be very poor far from this step. This allowance has been
   * added to simplify implementation of search algorithms near the
   * step endpoints.</p>
   * @param time time of the interpolated point
   * @return state at interpolated time
   */
  FieldODEStateAndDerivative<T> getInterpolatedState(T time);

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

}
