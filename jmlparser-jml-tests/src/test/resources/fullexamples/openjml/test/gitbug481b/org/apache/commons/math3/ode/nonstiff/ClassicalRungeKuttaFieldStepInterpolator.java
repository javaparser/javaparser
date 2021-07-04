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
 * This class implements a step interpolator for the classical fourth
 * order Runge-Kutta integrator.
 *
 * <p>This interpolator allows to compute dense output inside the last
 * step computed. The interpolation equation is consistent with the
 * integration scheme :
 * <ul>
 *   <li>Using reference point at step start:<br>
 *   y(t<sub>n</sub> + &theta; h) = y (t<sub>n</sub>)
 *                    + &theta; (h/6) [  (6 - 9 &theta; + 4 &theta;<sup>2</sup>) y'<sub>1</sub>
 *                                     + (    6 &theta; - 4 &theta;<sup>2</sup>) (y'<sub>2</sub> + y'<sub>3</sub>)
 *                                     + (   -3 &theta; + 4 &theta;<sup>2</sup>) y'<sub>4</sub>
 *                                    ]
 *   </li>
 *   <li>Using reference point at step end:<br>
 *   y(t<sub>n</sub> + &theta; h) = y (t<sub>n</sub> + h)
 *                    + (1 - &theta;) (h/6) [ (-4 &theta;^2 + 5 &theta; - 1) y'<sub>1</sub>
 *                                          +(4 &theta;^2 - 2 &theta; - 2) (y'<sub>2</sub> + y'<sub>3</sub>)
 *                                          -(4 &theta;^2 +   &theta; + 1) y'<sub>4</sub>
 *                                        ]
 *   </li>
 * </ul>
 * </p>
 *
 * where &theta; belongs to [0 ; 1] and where y'<sub>1</sub> to y'<sub>4</sub> are the four
 * evaluations of the derivatives already computed during the
 * step.</p>
 *
 * @see ClassicalRungeKuttaFieldIntegrator
 * @param <T> the type of the field elements
 * @since 3.6
 */

class ClassicalRungeKuttaFieldStepInterpolator<T extends RealFieldElement<T>>
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
    ClassicalRungeKuttaFieldStepInterpolator(final Field<T> field, final boolean forward,
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
    protected ClassicalRungeKuttaFieldStepInterpolator<T> create(final Field<T> newField, final boolean newForward, final T[][] newYDotK,
                                                                 final FieldODEStateAndDerivative<T> newGlobalPreviousState,
                                                                 final FieldODEStateAndDerivative<T> newGlobalCurrentState,
                                                                 final FieldODEStateAndDerivative<T> newSoftPreviousState,
                                                                 final FieldODEStateAndDerivative<T> newSoftCurrentState,
                                                                 final FieldEquationsMapper<T> newMapper) {
        return new ClassicalRungeKuttaFieldStepInterpolator<T>(newField, newForward, newYDotK,
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

        final T one                       = time.getField().getOne();
        final T oneMinusTheta             = one.subtract(theta);
        final T oneMinus2Theta            = one.subtract(theta.multiply(2));
        final T coeffDot1                 = oneMinusTheta.multiply(oneMinus2Theta);
        final T coeffDot23                = theta.multiply(oneMinusTheta).multiply(2);
        final T coeffDot4                 = theta.multiply(oneMinus2Theta).negate();
        final T[] interpolatedState;
        final T[] interpolatedDerivatives;

        if (getGlobalPreviousState() != null && theta.getReal() <= 0.5) {
            final T fourTheta2      = theta.multiply(theta).multiply(4);
            final T s               = thetaH.divide(6.0);
            final T coeff1          = s.multiply(fourTheta2.subtract(theta.multiply(9)).add(6));
            final T coeff23         = s.multiply(theta.multiply(6).subtract(fourTheta2));
            final T coeff4          = s.multiply(fourTheta2.subtract(theta.multiply(3)));
            interpolatedState       = previousStateLinearCombination(coeff1, coeff23, coeff23, coeff4);
            interpolatedDerivatives = derivativeLinearCombination(coeffDot1, coeffDot23, coeffDot23, coeffDot4);
        } else {
            final T fourTheta       = theta.multiply(4);
            final T s               = oneMinusThetaH.divide(6);
            final T coeff1          = s.multiply(theta.multiply(fourTheta.negate().add(5)).subtract(1));
            final T coeff23         = s.multiply(theta.multiply(fourTheta.subtract(2)).subtract(2));
            final T coeff4          = s.multiply(theta.multiply(fourTheta.negate().subtract(1)).subtract(1));
            interpolatedState       = currentStateLinearCombination(coeff1, coeff23, coeff23, coeff4);
            interpolatedDerivatives = derivativeLinearCombination(coeffDot1, coeffDot23, coeffDot23, coeffDot4);
        }

        return new FieldODEStateAndDerivative<T>(time, interpolatedState, interpolatedDerivatives);

    }

}
