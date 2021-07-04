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
 * This class implements a simple Euler integrator for Ordinary
 * Differential Equations.
 *
 * <p>The Euler algorithm is the simplest one that can be used to
 * integrate ordinary differential equations. It is a simple inversion
 * of the forward difference expression :
 * <code>f'=(f(t+h)-f(t))/h</code> which leads to
 * <code>f(t+h)=f(t)+hf'</code>. The interpolation scheme used for
 * dense output is the linear scheme already used for integration.</p>
 *
 * <p>This algorithm looks cheap because it needs only one function
 * evaluation per step. However, as it uses linear estimates, it needs
 * very small steps to achieve high accuracy, and small steps lead to
 * numerical errors and instabilities.</p>
 *
 * <p>This algorithm is almost never used and has been included in
 * this package only as a comparison reference for more useful
 * integrators.</p>
 *
 * @see MidpointFieldIntegrator
 * @see ClassicalRungeKuttaFieldIntegrator
 * @see GillFieldIntegrator
 * @see ThreeEighthesFieldIntegrator
 * @see LutherFieldIntegrator
 * @param <T> the type of the field elements
 * @since 3.6
 */

public class EulerFieldIntegrator<T extends RealFieldElement<T>> extends RungeKuttaFieldIntegrator<T> {

    /** Simple constructor.
     * Build an Euler integrator with the given step.
     * @param field field to which the time and state vector elements belong
     * @param step integration step
     */
    public EulerFieldIntegrator(final Field<T> field, final T step) {
        super(field, "Euler", step);
    }

    /** {@inheritDoc} */
    public T[] getC() {
        return MathArrays.buildArray(getField(), 0);
    }

    /** {@inheritDoc} */
    public T[][] getA() {
        return MathArrays.buildArray(getField(), 0, 0);
    }

    /** {@inheritDoc} */
    public T[] getB() {
        final T[] b = MathArrays.buildArray(getField(), 1);
        b[0] = getField().getOne();
        return b;
    }

    /** {@inheritDoc} */
    @Override
    protected EulerFieldStepInterpolator<T>
        createInterpolator(final boolean forward, T[][] yDotK,
                           final FieldODEStateAndDerivative<T> globalPreviousState,
                           final FieldODEStateAndDerivative<T> globalCurrentState,
                           final FieldEquationsMapper<T> mapper) {
        return new EulerFieldStepInterpolator<T>(getField(), forward, yDotK,
                                                 globalPreviousState, globalCurrentState,
                                                 globalPreviousState, globalCurrentState,
                                                 mapper);
    }

}
