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
import org.apache.commons.math3.ode.sampling.AbstractFieldStepInterpolator;
import org.apache.commons.math3.util.MathArrays;

/** This class represents an interpolator over the last step during an
 * ODE integration for Runge-Kutta and embedded Runge-Kutta integrators.
 *
 * @see RungeKuttaFieldIntegrator
 * @see EmbeddedRungeKuttaFieldIntegrator
 *
 * @param <T> the type of the field elements
 * @since 3.6
 */

abstract class RungeKuttaFieldStepInterpolator<T extends RealFieldElement<T>>
    extends AbstractFieldStepInterpolator<T> {

    /** Field to which the time and state vector elements belong. */
    private final Field<T> field;

    /** Slopes at the intermediate points. */
    private final T[][] yDotK;

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
    protected RungeKuttaFieldStepInterpolator(final Field<T> field, final boolean forward,
                                              final T[][] yDotK,
                                              final FieldODEStateAndDerivative<T> globalPreviousState,
                                              final FieldODEStateAndDerivative<T> globalCurrentState,
                                              final FieldODEStateAndDerivative<T> softPreviousState,
                                              final FieldODEStateAndDerivative<T> softCurrentState,
                                              final FieldEquationsMapper<T> mapper) {
        super(forward, globalPreviousState, globalCurrentState, softPreviousState, softCurrentState, mapper);
        this.field = field;
        this.yDotK = MathArrays.buildArray(field, yDotK.length, -1);
        for (int i = 0; i < yDotK.length; ++i) {
            this.yDotK[i] = yDotK[i].clone();
        }
    }

    /** {@inheritDoc} */
    @Override
    protected RungeKuttaFieldStepInterpolator<T> create(boolean newForward,
                                                        FieldODEStateAndDerivative<T> newGlobalPreviousState,
                                                        FieldODEStateAndDerivative<T> newGlobalCurrentState,
                                                        FieldODEStateAndDerivative<T> newSoftPreviousState,
                                                        FieldODEStateAndDerivative<T> newSoftCurrentState,
                                                        FieldEquationsMapper<T> newMapper) {
        return create(field, newForward, yDotK,
                      newGlobalPreviousState, newGlobalCurrentState,
                      newSoftPreviousState, newSoftCurrentState,
                      newMapper);
    }

    /** Create a new instance.
     * @param newField field to which the time and state vector elements belong
     * @param newForward integration direction indicator
     * @param newYDotK slopes at the intermediate points
     * @param newGlobalPreviousState start of the global step
     * @param newGlobalCurrentState end of the global step
     * @param newSoftPreviousState start of the restricted step
     * @param newSoftCurrentState end of the restricted step
     * @param newMapper equations mapper for the all equations
     * @return a new instance
     */
    protected abstract RungeKuttaFieldStepInterpolator<T> create(Field<T> newField, boolean newForward, T[][] newYDotK,
                                                                 FieldODEStateAndDerivative<T> newGlobalPreviousState,
                                                                 FieldODEStateAndDerivative<T> newGlobalCurrentState,
                                                                 FieldODEStateAndDerivative<T> newSoftPreviousState,
                                                                 FieldODEStateAndDerivative<T> newSoftCurrentState,
                                                                 FieldEquationsMapper<T> newMapper);

    /** Compute a state by linear combination added to previous state.
     * @param coefficients coefficients to apply to the method staged derivatives
     * @return combined state
     */
    protected final T[] previousStateLinearCombination(final T ... coefficients) {
        return combine(getPreviousState().getState(),
                       coefficients);
    }

    /** Compute a state by linear combination added to current state.
     * @param coefficients coefficients to apply to the method staged derivatives
     * @return combined state
     */
    protected T[] currentStateLinearCombination(final T ... coefficients) {
        return combine(getCurrentState().getState(),
                       coefficients);
    }

    /** Compute a state derivative by linear combination.
     * @param coefficients coefficients to apply to the method staged derivatives
     * @return combined state
     */
    protected T[] derivativeLinearCombination(final T ... coefficients) {
        return combine(MathArrays.buildArray(field, yDotK[0].length), coefficients);
    }

    /** Linearly combine arrays.
     * @param a array to add to
     * @param coefficients coefficients to apply to the method staged derivatives
     * @return a itself, as a convenience for fluent API
     */
    private T[] combine(final T[] a, final T ... coefficients) {
        for (int i = 0; i < a.length; ++i) {
            for (int k = 0; k < coefficients.length; ++k) {
                a[i] = a[i].add(coefficients[k].multiply(yDotK[k][i]));
            }
        }
        return a;
    }

}
