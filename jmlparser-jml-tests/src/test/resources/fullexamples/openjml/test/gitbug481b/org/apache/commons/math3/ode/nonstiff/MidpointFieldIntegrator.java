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
import org.apache.commons.math3.util.MathArrays;

/**
 * This class implements a second order Runge-Kutta integrator for
 * Ordinary Differential Equations.
 *
 * <p>This method is an explicit Runge-Kutta method, its Butcher-array
 * is the following one :
 * <pre>
 *    0  |  0    0
 *   1/2 | 1/2   0
 *       |----------
 *       |  0    1
 * </pre>
 * </p>
 *
 * @see EulerFieldIntegrator
 * @see ClassicalRungeKuttaFieldIntegrator
 * @see GillFieldIntegrator
 * @see ThreeEighthesFieldIntegrator
 * @see LutherFieldIntegrator
 *
 * @param <T> the type of the field elements
 * @since 3.6
 */

public class MidpointFieldIntegrator<T extends RealFieldElement<T>> extends RungeKuttaFieldIntegrator<T> {

    /** Simple constructor.
     * Build a midpoint integrator with the given step.
     * @param field field to which the time and state vector elements belong
     * @param step integration step
     */
    public MidpointFieldIntegrator(final Field<T> field, final T step) {
        super(field, "midpoint", step);
    }

    /** {@inheritDoc} */
    public T[] getC() {
        final T[] c = MathArrays.buildArray(getField(), 1);
        c[0] = getField().getOne().multiply(0.5);
        return c;
    }

    /** {@inheritDoc} */
    public T[][] getA() {
        final T[][] a = MathArrays.buildArray(getField(), 1, 1);
        a[0][0] = fraction(1, 2);
        return a;
    }

    /** {@inheritDoc} */
    public T[] getB() {
        final T[] b = MathArrays.buildArray(getField(), 2);
        b[0] = getField().getZero();
        b[1] = getField().getOne();
        return b;
    }

    /** {@inheritDoc} */
    @Override
    protected MidpointFieldStepInterpolator<T>
        createInterpolator(final boolean forward, T[][] yDotK,
                           final FieldODEStateAndDerivative<T> globalPreviousState,
                           final FieldODEStateAndDerivative<T> globalCurrentState,
                           final FieldEquationsMapper<T> mapper) {
        return new MidpointFieldStepInterpolator<T>(getField(), forward, yDotK,
                                                    globalPreviousState, globalCurrentState,
                                                    globalPreviousState, globalCurrentState,
                                                    mapper);
    }

}
