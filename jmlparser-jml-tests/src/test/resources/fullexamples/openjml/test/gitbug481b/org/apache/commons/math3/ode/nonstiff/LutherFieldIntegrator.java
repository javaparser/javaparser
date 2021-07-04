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
 * This class implements the Luther sixth order Runge-Kutta
 * integrator for Ordinary Differential Equations.

 * <p>
 * This method is described in H. A. Luther 1968 paper <a
 * href="http://www.ams.org/journals/mcom/1968-22-102/S0025-5718-68-99876-1/S0025-5718-68-99876-1.pdf">
 * An explicit Sixth-Order Runge-Kutta Formula</a>.
 * </p>

 * <p>This method is an explicit Runge-Kutta method, its Butcher-array
 * is the following one :
 * <pre>
 *        0   |               0                     0                     0                     0                     0                     0
 *        1   |               1                     0                     0                     0                     0                     0
 *       1/2  |              3/8                   1/8                    0                     0                     0                     0
 *       2/3  |              8/27                  2/27                  8/27                   0                     0                     0
 *   (7-q)/14 | (  -21 +   9q)/392    (  -56 +   8q)/392    (  336 -  48q)/392    (  -63 +   3q)/392                  0                     0
 *   (7+q)/14 | (-1155 - 255q)/1960   ( -280 -  40q)/1960   (    0 - 320q)/1960   (   63 + 363q)/1960   ( 2352 + 392q)/1960                 0
 *        1   | (  330 + 105q)/180    (  120 +   0q)/180    ( -200 + 280q)/180    (  126 - 189q)/180    ( -686 - 126q)/180     ( 490 -  70q)/180
 *            |--------------------------------------------------------------------------------------------------------------------------------------------------
 *            |              1/20                   0                   16/45                  0                   49/180                 49/180         1/20
 * </pre>
 * where q = &radic;21</p>
 *
 * @see EulerFieldIntegrator
 * @see ClassicalRungeKuttaFieldIntegrator
 * @see GillFieldIntegrator
 * @see MidpointFieldIntegrator
 * @see ThreeEighthesFieldIntegrator
 * @param <T> the type of the field elements
 * @since 3.6
 */

public class LutherFieldIntegrator<T extends RealFieldElement<T>>
    extends RungeKuttaFieldIntegrator<T> {

    /** Simple constructor.
     * Build a fourth-order Luther integrator with the given step.
     * @param field field to which the time and state vector elements belong
     * @param step integration step
     */
    public LutherFieldIntegrator(final Field<T> field, final T step) {
        super(field, "Luther", step);
    }

    /** {@inheritDoc} */
    public T[] getC() {
        final T q = getField().getZero().add(21).sqrt();
        final T[] c = MathArrays.buildArray(getField(), 6);
        c[0] = getField().getOne();
        c[1] = fraction(1, 2);
        c[2] = fraction(2, 3);
        c[3] = q.subtract(7).divide(-14);
        c[4] = q.add(7).divide(14);
        c[5] = getField().getOne();
        return c;
    }

    /** {@inheritDoc} */
    public T[][] getA() {
        final T q = getField().getZero().add(21).sqrt();
        final T[][] a = MathArrays.buildArray(getField(), 6, -1);
        for (int i = 0; i < a.length; ++i) {
            a[i] = MathArrays.buildArray(getField(), i + 1);
        }
        a[0][0] = getField().getOne();
        a[1][0] = fraction(3,  8);
        a[1][1] = fraction(1,  8);
        a[2][0] = fraction(8, 27);
        a[2][1] = fraction(2, 27);
        a[2][2] = a[2][0];
        a[3][0] = q.multiply(   9).add(  -21).divide( 392);
        a[3][1] = q.multiply(   8).add(  -56).divide( 392);
        a[3][2] = q.multiply( -48).add(  336).divide( 392);
        a[3][3] = q.multiply(   3).add(  -63).divide( 392);
        a[4][0] = q.multiply(-255).add(-1155).divide(1960);
        a[4][1] = q.multiply( -40).add( -280).divide(1960);
        a[4][2] = q.multiply(-320)           .divide(1960);
        a[4][3] = q.multiply( 363).add(   63).divide(1960);
        a[4][4] = q.multiply( 392).add( 2352).divide(1960);
        a[5][0] = q.multiply( 105).add(  330).divide( 180);
        a[5][1] = fraction(2, 3);
        a[5][2] = q.multiply( 280).add( -200).divide( 180);
        a[5][3] = q.multiply(-189).add(  126).divide( 180);
        a[5][4] = q.multiply(-126).add( -686).divide( 180);
        a[5][5] = q.multiply( -70).add(  490).divide( 180);
        return a;
    }

    /** {@inheritDoc} */
    public T[] getB() {

        final T[] b = MathArrays.buildArray(getField(), 7);
        b[0] = fraction( 1,  20);
        b[1] = getField().getZero();
        b[2] = fraction(16,  45);
        b[3] = getField().getZero();
        b[4] = fraction(49, 180);
        b[5] = b[4];
        b[6] = b[0];

        return b;

    }

    /** {@inheritDoc} */
    @Override
    protected LutherFieldStepInterpolator<T>
        createInterpolator(final boolean forward, T[][] yDotK,
                           final FieldODEStateAndDerivative<T> globalPreviousState,
                           final FieldODEStateAndDerivative<T> globalCurrentState,
                           final FieldEquationsMapper<T> mapper) {
        return new LutherFieldStepInterpolator<T>(getField(), forward, yDotK,
                                                  globalPreviousState, globalCurrentState,
                                                  globalPreviousState, globalCurrentState,
                                                  mapper);
    }

}
