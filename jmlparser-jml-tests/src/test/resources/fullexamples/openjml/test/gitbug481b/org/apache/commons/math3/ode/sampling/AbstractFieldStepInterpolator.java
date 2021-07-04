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
import org.apache.commons.math3.ode.FieldEquationsMapper;
import org.apache.commons.math3.ode.FieldODEStateAndDerivative;

/** This abstract class represents an interpolator over the last step
 * during an ODE integration.
 *
 * <p>The various ODE integrators provide objects extending this class
 * to the step handlers. The handlers can use these objects to
 * retrieve the state vector at intermediate times between the
 * previous and the current grid points (dense output).</p>
 *
 * @see org.apache.commons.math3.ode.FirstOrderFieldIntegrator
 * @see StepHandler
 *
 * @param <T> the type of the field elements
 * @since 3.6
 */

public abstract class AbstractFieldStepInterpolator<T extends RealFieldElement<T>>
    implements FieldStepInterpolator<T> {

    /** Global previous state. */
    private final FieldODEStateAndDerivative<T> globalPreviousState;

    /** Global current state. */
    private final FieldODEStateAndDerivative<T> globalCurrentState;

    /** Soft previous state. */
    private final FieldODEStateAndDerivative<T> softPreviousState;

    /** Soft current state. */
    private final FieldODEStateAndDerivative<T> softCurrentState;

    /** integration direction. */
    private final boolean forward;

    /** Mapper for ODE equations primary and secondary components. */
    private FieldEquationsMapper<T> mapper;

    /** Simple constructor.
     * @param isForward integration direction indicator
     * @param globalPreviousState start of the global step
     * @param globalCurrentState end of the global step
     * @param softPreviousState start of the restricted step
     * @param softCurrentState end of the restricted step
     * @param equationsMapper mapper for ODE equations primary and secondary components
     */
    protected AbstractFieldStepInterpolator(final boolean isForward,
                                            final FieldODEStateAndDerivative<T> globalPreviousState,
                                            final FieldODEStateAndDerivative<T> globalCurrentState,
                                            final FieldODEStateAndDerivative<T> softPreviousState,
                                            final FieldODEStateAndDerivative<T> softCurrentState,
                                            final FieldEquationsMapper<T> equationsMapper) {
        this.forward             = isForward;
        this.globalPreviousState = globalPreviousState;
        this.globalCurrentState  = globalCurrentState;
        this.softPreviousState   = softPreviousState;
        this.softCurrentState    = softCurrentState;
        this.mapper              = equationsMapper;
    }

    /** Create a new restricted version of the instance.
     * <p>
     * The instance is not changed at all.
     * </p>
     * @param previousState start of the restricted step
     * @param currentState end of the restricted step
     * @return restricted version of the instance
     * @see #getPreviousState()
     * @see #getCurrentState()
     */
    public AbstractFieldStepInterpolator<T> restrictStep(final FieldODEStateAndDerivative<T> previousState,
                                                         final FieldODEStateAndDerivative<T> currentState) {
        return create(forward, globalPreviousState, globalCurrentState, previousState, currentState, mapper);
    }

    /** Create a new instance.
     * @param newForward integration direction indicator
     * @param newGlobalPreviousState start of the global step
     * @param newGlobalCurrentState end of the global step
     * @param newSoftPreviousState start of the restricted step
     * @param newSoftCurrentState end of the restricted step
     * @param newMapper equations mapper for the all equations
     * @return a new instance
     */
    protected abstract AbstractFieldStepInterpolator<T> create(boolean newForward,
                                                               FieldODEStateAndDerivative<T> newGlobalPreviousState,
                                                               FieldODEStateAndDerivative<T> newGlobalCurrentState,
                                                               FieldODEStateAndDerivative<T> newSoftPreviousState,
                                                               FieldODEStateAndDerivative<T> newSoftCurrentState,
                                                               FieldEquationsMapper<T> newMapper);

    /**
     * Get the previous global grid point state.
     * @return previous global grid point state
     */
    public FieldODEStateAndDerivative<T> getGlobalPreviousState() {
        return globalPreviousState;
    }

    /**
     * Get the current global grid point state.
     * @return current global grid point state
     */
    public FieldODEStateAndDerivative<T> getGlobalCurrentState() {
        return globalCurrentState;
    }

    /** {@inheritDoc} */
    public FieldODEStateAndDerivative<T> getPreviousState() {
        return softPreviousState;
    }

    /** {@inheritDoc} */
    public FieldODEStateAndDerivative<T> getCurrentState() {
        return softCurrentState;
    }

    /** {@inheritDoc} */
    public FieldODEStateAndDerivative<T> getInterpolatedState(final T time) {
        final T thetaH         = time.subtract(globalPreviousState.getTime());
        final T oneMinusThetaH = globalCurrentState.getTime().subtract(time);
        final T theta          = thetaH.divide(globalCurrentState.getTime().subtract(globalPreviousState.getTime()));
        return computeInterpolatedStateAndDerivatives(mapper, time, theta, thetaH, oneMinusThetaH);
    }

    /** {@inheritDoc} */
    public boolean isForward() {
        return forward;
    }

    /** Compute the state and derivatives at the interpolated time.
     * This is the main processing method that should be implemented by
     * the derived classes to perform the interpolation.
     * @param equationsMapper mapper for ODE equations primary and secondary components
     * @param time interpolation time
     * @param theta normalized interpolation abscissa within the step
     * (theta is zero at the previous time step and one at the current time step)
     * @param thetaH time gap between the previous time and the interpolated time
     * @param oneMinusThetaH time gap between the interpolated time and
     * the current time
     * @return interpolated state and derivatives
     * @exception MaxCountExceededException if the number of functions evaluations is exceeded
     */
    protected abstract FieldODEStateAndDerivative<T> computeInterpolatedStateAndDerivatives(FieldEquationsMapper<T> equationsMapper,
                                                                                            T time, T theta,
                                                                                            T thetaH, T oneMinusThetaH)
        throws MaxCountExceededException;

}
