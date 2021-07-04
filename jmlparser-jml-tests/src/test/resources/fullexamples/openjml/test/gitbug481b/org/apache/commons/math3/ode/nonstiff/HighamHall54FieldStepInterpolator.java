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
 * This class represents an interpolator over the last step during an
 * ODE integration for the 5(4) Higham and Hall integrator.
 *
 * @see HighamHall54FieldIntegrator
 *
 * @param <T> the type of the field elements
 * @since 3.6
 */

class HighamHall54FieldStepInterpolator<T extends RealFieldElement<T>>
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
    HighamHall54FieldStepInterpolator(final Field<T> field, final boolean forward,
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
    protected HighamHall54FieldStepInterpolator<T> create(final Field<T> newField, final boolean newForward, final T[][] newYDotK,
                                                          final FieldODEStateAndDerivative<T> newGlobalPreviousState,
                                                          final FieldODEStateAndDerivative<T> newGlobalCurrentState,
                                                          final FieldODEStateAndDerivative<T> newSoftPreviousState,
                                                          final FieldODEStateAndDerivative<T> newSoftCurrentState,
                                                          final FieldEquationsMapper<T> newMapper) {
        return new HighamHall54FieldStepInterpolator<T>(newField, newForward, newYDotK,
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

        final T bDot0 = theta.multiply(theta.multiply(theta.multiply( -10.0      ).add( 16.0       )).add(-15.0 /  2.0)).add(1);
        final T bDot1 = time.getField().getZero();
        final T bDot2 = theta.multiply(theta.multiply(theta.multiply( 135.0 / 2.0).add(-729.0 / 8.0)).add(459.0 / 16.0));
        final T bDot3 = theta.multiply(theta.multiply(theta.multiply(-120.0      ).add( 152.0      )).add(-44.0       ));
        final T bDot4 = theta.multiply(theta.multiply(theta.multiply( 125.0 / 2.0).add(-625.0 / 8.0)).add(375.0 / 16.0));
        final T bDot5 = theta.multiply(  5.0 /  8.0).multiply(theta.multiply(2).subtract(1));
        final T[] interpolatedState;
        final T[] interpolatedDerivatives;

        if (getGlobalPreviousState() != null && theta.getReal() <= 0.5) {
            final T b0 = thetaH.multiply(theta.multiply(theta.multiply(theta.multiply( -5.0 / 2.0).add(  16.0 /  3.0)).add(-15.0 /  4.0)).add(1));
            final T b1 = time.getField().getZero();
            final T b2 = thetaH.multiply(theta.multiply(theta.multiply(theta.multiply(135.0 / 8.0).add(-243.0 /  8.0)).add(459.0 / 32.0)));
            final T b3 = thetaH.multiply(theta.multiply(theta.multiply(theta.multiply(-30.0      ).add( 152.0 /  3.0)).add(-22.0       )));
            final T b4 = thetaH.multiply(theta.multiply(theta.multiply(theta.multiply(125.0 / 8.0).add(-625.0 / 24.0)).add(375.0 / 32.0)));
            final T b5 = thetaH.multiply(theta.multiply(theta.multiply(                                   5.0 / 12.0 ).add( -5.0 / 16.0)));
            interpolatedState       = previousStateLinearCombination(b0, b1, b2, b3, b4, b5);
            interpolatedDerivatives = derivativeLinearCombination(bDot0, bDot1, bDot2, bDot3, bDot4, bDot5);
        } else {
            final T theta2 = theta.multiply(theta);
            final T h      = thetaH.divide(theta);
            final T b0 = h.multiply( theta.multiply(theta.multiply(theta.multiply(theta.multiply(-5.0 / 2.0).add( 16.0 / 3.0)).add( -15.0 /  4.0)).add(  1.0       )).add(  -1.0 / 12.0));
            final T b1 = time.getField().getZero();
            final T b2 = h.multiply(theta2.multiply(theta.multiply(theta.multiply(                               135.0 / 8.0 ).add(-243.0 /  8.0)).add(459.0 / 32.0)).add( -27.0 / 32.0));
            final T b3 = h.multiply(theta2.multiply(theta.multiply(theta.multiply(                               -30.0       ).add( 152.0 /  3.0)).add(-22.0       )).add(  4.0  /  3.0));
            final T b4 = h.multiply(theta2.multiply(theta.multiply(theta.multiply(                               125.0 / 8.0 ).add(-625.0 / 24.0)).add(375.0 / 32.0)).add(-125.0 / 96.0));
            final T b5 = h.multiply(theta2.multiply(theta.multiply(                                                                   5.0 / 12.0 ).add(-5.0  / 16.0)).add(  -5.0 / 48.0));
            interpolatedState       = currentStateLinearCombination(b0, b1, b2, b3, b4, b5);
            interpolatedDerivatives = derivativeLinearCombination(bDot0, bDot1, bDot2, bDot3, bDot4, bDot5);
        }

        return new FieldODEStateAndDerivative<T>(time, interpolatedState, interpolatedDerivatives);

    }

}
