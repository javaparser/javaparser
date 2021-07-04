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
import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.MaxCountExceededException;
import org.apache.commons.math3.exception.NoBracketingException;
import org.apache.commons.math3.exception.NumberIsTooSmallException;
import org.apache.commons.math3.ode.AbstractFieldIntegrator;
import org.apache.commons.math3.ode.FieldEquationsMapper;
import org.apache.commons.math3.ode.FieldExpandableODE;
import org.apache.commons.math3.ode.FirstOrderFieldDifferentialEquations;
import org.apache.commons.math3.ode.FieldODEState;
import org.apache.commons.math3.ode.FieldODEStateAndDerivative;
import org.apache.commons.math3.util.MathArrays;

/**
 * This class implements the common part of all fixed step Runge-Kutta
 * integrators for Ordinary Differential Equations.
 *
 * <p>These methods are explicit Runge-Kutta methods, their Butcher
 * arrays are as follows :
 * <pre>
 *    0  |
 *   c2  | a21
 *   c3  | a31  a32
 *   ... |        ...
 *   cs  | as1  as2  ...  ass-1
 *       |--------------------------
 *       |  b1   b2  ...   bs-1  bs
 * </pre>
 * </p>
 *
 * @see EulerFieldIntegrator
 * @see ClassicalRungeKuttaFieldIntegrator
 * @see GillFieldIntegrator
 * @see MidpointFieldIntegrator
 * @param <T> the type of the field elements
 * @since 3.6
 */

public abstract class RungeKuttaFieldIntegrator<T extends RealFieldElement<T>>
    extends AbstractFieldIntegrator<T>
    implements FieldButcherArrayProvider<T> {

    /** Time steps from Butcher array (without the first zero). */
    private final T[] c;

    /** Internal weights from Butcher array (without the first empty row). */
    private final T[][] a;

    /** External weights for the high order method from Butcher array. */
    private final T[] b;

    /** Integration step. */
    private final T step;

    /** Simple constructor.
     * Build a Runge-Kutta integrator with the given
     * step. The default step handler does nothing.
     * @param field field to which the time and state vector elements belong
     * @param name name of the method
     * @param step integration step
     */
    protected RungeKuttaFieldIntegrator(final Field<T> field, final String name, final T step) {
        super(field, name);
        this.c    = getC();
        this.a    = getA();
        this.b    = getB();
        this.step = step.abs();
    }

    /** Create a fraction.
     * @param p numerator
     * @param q denominator
     * @return p/q computed in the instance field
     */
    protected T fraction(final int p, final int q) {
        return getField().getZero().add(p).divide(q);
    }

    /** Create an interpolator.
     * @param forward integration direction indicator
     * @param yDotK slopes at the intermediate points
     * @param globalPreviousState start of the global step
     * @param globalCurrentState end of the global step
     * @param mapper equations mapper for the all equations
     * @return external weights for the high order method from Butcher array
     */
    protected abstract RungeKuttaFieldStepInterpolator<T> createInterpolator(boolean forward, T[][] yDotK,
                                                                             final FieldODEStateAndDerivative<T> globalPreviousState,
                                                                             final FieldODEStateAndDerivative<T> globalCurrentState,
                                                                             FieldEquationsMapper<T> mapper);

    /** {@inheritDoc} */
    public FieldODEStateAndDerivative<T> integrate(final FieldExpandableODE<T> equations,
                                                   final FieldODEState<T> initialState, final T finalTime)
        throws NumberIsTooSmallException, DimensionMismatchException,
        MaxCountExceededException, NoBracketingException {

        sanityChecks(initialState, finalTime);
        final T   t0 = initialState.getTime();
        final T[] y0 = equations.getMapper().mapState(initialState);
        setStepStart(initIntegration(equations, t0, y0, finalTime));
        final boolean forward = finalTime.subtract(initialState.getTime()).getReal() > 0;

        // create some internal working arrays
        final int   stages = c.length + 1;
        T[]         y      = y0;
        final T[][] yDotK  = MathArrays.buildArray(getField(), stages, -1);
        final T[]   yTmp   = MathArrays.buildArray(getField(), y0.length);

        // set up integration control objects
        if (forward) {
            if (getStepStart().getTime().add(step).subtract(finalTime).getReal() >= 0) {
                setStepSize(finalTime.subtract(getStepStart().getTime()));
            } else {
                setStepSize(step);
            }
        } else {
            if (getStepStart().getTime().subtract(step).subtract(finalTime).getReal() <= 0) {
                setStepSize(finalTime.subtract(getStepStart().getTime()));
            } else {
                setStepSize(step.negate());
            }
        }

        // main integration loop
        setIsLastStep(false);
        do {

            // first stage
            y        = equations.getMapper().mapState(getStepStart());
            yDotK[0] = equations.getMapper().mapDerivative(getStepStart());

            // next stages
            for (int k = 1; k < stages; ++k) {

                for (int j = 0; j < y0.length; ++j) {
                    T sum = yDotK[0][j].multiply(a[k-1][0]);
                    for (int l = 1; l < k; ++l) {
                        sum = sum.add(yDotK[l][j].multiply(a[k-1][l]));
                    }
                    yTmp[j] = y[j].add(getStepSize().multiply(sum));
                }

                yDotK[k] = computeDerivatives(getStepStart().getTime().add(getStepSize().multiply(c[k-1])), yTmp);

            }

            // estimate the state at the end of the step
            for (int j = 0; j < y0.length; ++j) {
                T sum = yDotK[0][j].multiply(b[0]);
                for (int l = 1; l < stages; ++l) {
                    sum = sum.add(yDotK[l][j].multiply(b[l]));
                }
                yTmp[j] = y[j].add(getStepSize().multiply(sum));
            }
            final T stepEnd   = getStepStart().getTime().add(getStepSize());
            final T[] yDotTmp = computeDerivatives(stepEnd, yTmp);
            final FieldODEStateAndDerivative<T> stateTmp = new FieldODEStateAndDerivative<T>(stepEnd, yTmp, yDotTmp);

            // discrete events handling
            System.arraycopy(yTmp, 0, y, 0, y0.length);
            setStepStart(acceptStep(createInterpolator(forward, yDotK, getStepStart(), stateTmp, equations.getMapper()),
                                    finalTime));

            if (!isLastStep()) {

                // stepsize control for next step
                final T  nextT      = getStepStart().getTime().add(getStepSize());
                final boolean nextIsLast = forward ?
                                           (nextT.subtract(finalTime).getReal() >= 0) :
                                           (nextT.subtract(finalTime).getReal() <= 0);
                if (nextIsLast) {
                    setStepSize(finalTime.subtract(getStepStart().getTime()));
                }
            }

        } while (!isLastStep());

        final FieldODEStateAndDerivative<T> finalState = getStepStart();
        setStepStart(null);
        setStepSize(null);
        return finalState;

    }

    /** Fast computation of a single step of ODE integration.
     * <p>This method is intended for the limited use case of
     * very fast computation of only one step without using any of the
     * rich features of general integrators that may take some time
     * to set up (i.e. no step handlers, no events handlers, no additional
     * states, no interpolators, no error control, no evaluations count,
     * no sanity checks ...). It handles the strict minimum of computation,
     * so it can be embedded in outer loops.</p>
     * <p>
     * This method is <em>not</em> used at all by the {@link #integrate(FieldExpandableODE,
     * FieldODEState, RealFieldElement)} method. It also completely ignores the step set at
     * construction time, and uses only a single step to go from {@code t0} to {@code t}.
     * </p>
     * <p>
     * As this method does not use any of the state-dependent features of the integrator,
     * it should be reasonably thread-safe <em>if and only if</em> the provided differential
     * equations are themselves thread-safe.
     * </p>
     * @param equations differential equations to integrate
     * @param t0 initial time
     * @param y0 initial value of the state vector at t0
     * @param t target time for the integration
     * (can be set to a value smaller than {@code t0} for backward integration)
     * @return state vector at {@code t}
     */
    public T[] singleStep(final FirstOrderFieldDifferentialEquations<T> equations,
                          final T t0, final T[] y0, final T t) {

        // create some internal working arrays
        final T[] y       = y0.clone();
        final int stages  = c.length + 1;
        final T[][] yDotK = MathArrays.buildArray(getField(), stages, -1);
        final T[] yTmp    = y0.clone();

        // first stage
        final T h = t.subtract(t0);
        yDotK[0] = equations.computeDerivatives(t0, y);

        // next stages
        for (int k = 1; k < stages; ++k) {

            for (int j = 0; j < y0.length; ++j) {
                T sum = yDotK[0][j].multiply(a[k-1][0]);
                for (int l = 1; l < k; ++l) {
                    sum = sum.add(yDotK[l][j].multiply(a[k-1][l]));
                }
                yTmp[j] = y[j].add(h.multiply(sum));
            }

            yDotK[k] = equations.computeDerivatives(t0.add(h.multiply(c[k-1])), yTmp);

        }

        // estimate the state at the end of the step
        for (int j = 0; j < y0.length; ++j) {
            T sum = yDotK[0][j].multiply(b[0]);
            for (int l = 1; l < stages; ++l) {
                sum = sum.add(yDotK[l][j].multiply(b[l]));
            }
            y[j] = y[j].add(h.multiply(sum));
        }

        return y;

    }

}
