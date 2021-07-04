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

package org.apache.commons.math3.ode.nonstiff;

import org.apache.commons.math3.Field;
import org.apache.commons.math3.RealFieldElement;
import org.apache.commons.math3.ode.FieldEquationsMapper;
import org.apache.commons.math3.ode.FieldODEStateAndDerivative;

/**
 * This class implements a linear interpolator for step.
 *
 * <p>This interpolator computes dense output inside the last
 * step computed. The interpolation equation is consistent with the
 * integration scheme :
 * <ul>
 *   <li>Using reference point at step start:<br>
 *     y(t<sub>n</sub> + &theta; h) = y (t<sub>n</sub>) + &theta; h y'
 *   </li>
 *   <li>Using reference point at step end:<br>
 *     y(t<sub>n</sub> + &theta; h) = y (t<sub>n</sub> + h) - (1-&theta;) h y'
 *   </li>
 * </ul>
 * </p>
 *
 * where &theta; belongs to [0 ; 1] and where y' is the evaluation of
 * the derivatives already computed during the step.</p>
 *
 * @see EulerFieldIntegrator
 * @param <T> the type of the field elements
 * @since 3.6
 */

class EulerFieldStepInterpolator<T extends RealFieldElement<T>>
    extends RungeKuttaFieldStepInterpolator<T> {

    /** Simple constructor.
     * @param field field to which the time and state vector elements belong
     * @param forward integration direction indicator
     * @param yDotK slopes at the intermediate points
     * @param globalPreviousState start of the global step
     * @param globalCurrentState end of the global step
     * @param softPreviousState start of the restricted step
     * @param softCurrentState end of the restricted step
     * @param mapper equations mapper for the all equations
     */
    EulerFieldStepInterpolator(final Field<T> field, final boolean forward,
                                             final T[][] yDotK,
                                             final FieldODEStateAndDerivative<T> globalPreviousState,
                                             final FieldODEStateAndDerivative<T> globalCurrentState,
                                             final FieldODEStateAndDerivative<T> softPreviousState,
                                             final FieldODEStateAndDerivative<T> softCurrentState,
                                             final FieldEquationsMapper<T> mapper) {
        super(field, forward, yDotK,
              globalPreviousState, globalCurrentState, softPreviousState, softCurrentState,
              mapper);
    }

    /** {@inheritDoc} */
    @Override
    protected EulerFieldStepInterpolator<T> create(final Field<T> newField, final boolean newForward, final T[][] newYDotK,
                                                                 final FieldODEStateAndDerivative<T> newGlobalPreviousState,
                                                                 final FieldODEStateAndDerivative<T> newGlobalCurrentState,
                                                                 final FieldODEStateAndDerivative<T> newSoftPreviousState,
                                                                 final FieldODEStateAndDerivative<T> newSoftCurrentState,
                                                                 final FieldEquationsMapper<T> newMapper) {
        return new EulerFieldStepInterpolator<T>(newField, newForward, newYDotK,
                                                 newGlobalPreviousState, newGlobalCurrentState,
                                                 newSoftPreviousState, newSoftCurrentState,
                                                 newMapper);
    }

    /** {@inheritDoc} */
    @SuppressWarnings("unchecked")
    @Override
    protected FieldODEStateAndDerivative<T> computeInterpolatedStateAndDerivatives(final FieldEquationsMapper<T> mapper,
                                                                                   final T time, final T theta,
                                                                                   final T thetaH, final T oneMinusThetaH) {
        final T[] interpolatedState;
        final T[] interpolatedDerivatives;
        if (getGlobalPreviousState() != null && theta.getReal() <= 0.5) {
            interpolatedState       = previousStateLinearCombination(thetaH);
            interpolatedDerivatives = derivativeLinearCombination(time.getField().getOne());
        } else {
            interpolatedState       = currentStateLinearCombination(oneMinusThetaH.negate());
            interpolatedDerivatives = derivativeLinearCombination(time.getField().getOne());
        }

        return new FieldODEStateAndDerivative<T>(time, interpolatedState, interpolatedDerivatives);

    }

}
