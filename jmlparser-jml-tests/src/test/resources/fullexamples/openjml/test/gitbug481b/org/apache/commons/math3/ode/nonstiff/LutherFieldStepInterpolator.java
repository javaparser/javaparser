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
 * ODE integration for the 6th order Luther integrator.
 *
 * <p>This interpolator computes dense output inside the last
 * step computed. The interpolation equation is consistent with the
 * integration scheme.</p>
 *
 * @see LutherFieldIntegrator
 * @param <T> the type of the field elements
 * @since 3.6
 */

class LutherFieldStepInterpolator<T extends RealFieldElement<T>>
    extends RungeKuttaFieldStepInterpolator<T> {

    /** -49 - 49 q. */
    private final T c5a;

    /** 392 + 287 q. */
    private final T c5b;

    /** -637 - 357 q. */
    private final T c5c;

    /** 833 + 343 q. */
    private final T c5d;

    /** -49 + 49 q. */
    private final T c6a;

    /** -392 - 287 q. */
    private final T c6b;

    /** -637 + 357 q. */
    private final T c6c;

    /** 833 - 343 q. */
    private final T c6d;

    /** 49 + 49 q. */
    private final T d5a;

    /** -1372 - 847 q. */
    private final T d5b;

    /** 2254 + 1029 q */
    private final T d5c;

    /** 49 - 49 q. */
    private final T d6a;

    /** -1372 + 847 q. */
    private final T d6b;

    /** 2254 - 1029 q */
    private final T d6c;

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
    LutherFieldStepInterpolator(final Field<T> field, final boolean forward,
                                final T[][] yDotK,
                                final FieldODEStateAndDerivative<T> globalPreviousState,
                                final FieldODEStateAndDerivative<T> globalCurrentState,
                                final FieldODEStateAndDerivative<T> softPreviousState,
                                final FieldODEStateAndDerivative<T> softCurrentState,
                                final FieldEquationsMapper<T> mapper) {
        super(field, forward, yDotK,
              globalPreviousState, globalCurrentState, softPreviousState, softCurrentState,
              mapper);
        final T q = field.getZero().add(21).sqrt();
        c5a = q.multiply(  -49).add(  -49);
        c5b = q.multiply(  287).add(  392);
        c5c = q.multiply( -357).add( -637);
        c5d = q.multiply(  343).add(  833);
        c6a = q.multiply(   49).add(  -49);
        c6b = q.multiply( -287).add(  392);
        c6c = q.multiply(  357).add( -637);
        c6d = q.multiply( -343).add(  833);
        d5a = q.multiply(   49).add(   49);
        d5b = q.multiply( -847).add(-1372);
        d5c = q.multiply( 1029).add( 2254);
        d6a = q.multiply(  -49).add(   49);
        d6b = q.multiply(  847).add(-1372);
        d6c = q.multiply(-1029).add( 2254);
    }

    /** {@inheritDoc} */
    @Override
    protected LutherFieldStepInterpolator<T> create(final Field<T> newField, final boolean newForward, final T[][] newYDotK,
                                                    final FieldODEStateAndDerivative<T> newGlobalPreviousState,
                                                    final FieldODEStateAndDerivative<T> newGlobalCurrentState,
                                                    final FieldODEStateAndDerivative<T> newSoftPreviousState,
                                                    final FieldODEStateAndDerivative<T> newSoftCurrentState,
                                                    final FieldEquationsMapper<T> newMapper) {
        return new LutherFieldStepInterpolator<T>(newField, newForward, newYDotK,
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

        // the coefficients below have been computed by solving the
        // order conditions from a theorem from Butcher (1963), using
        // the method explained in Folkmar Bornemann paper "Runge-Kutta
        // Methods, Trees, and Maple", Center of Mathematical Sciences, Munich
        // University of Technology, February 9, 2001
        //<http://wwwzenger.informatik.tu-muenchen.de/selcuk/sjam012101.html>

        // the method is implemented in the rkcheck tool
        // <https://www.spaceroots.org/software/rkcheck/index.html>.
        // Running it for order 5 gives the following order conditions
        // for an interpolator:
        // order 1 conditions
        // \sum_{i=1}^{i=s}\left(b_{i} \right) =1
        // order 2 conditions
        // \sum_{i=1}^{i=s}\left(b_{i} c_{i}\right) = \frac{\theta}{2}
        // order 3 conditions
        // \sum_{i=2}^{i=s}\left(b_{i} \sum_{j=1}^{j=i-1}{\left(a_{i,j} c_{j} \right)}\right) = \frac{\theta^{2}}{6}
        // \sum_{i=1}^{i=s}\left(b_{i} c_{i}^{2}\right) = \frac{\theta^{2}}{3}
        // order 4 conditions
        // \sum_{i=3}^{i=s}\left(b_{i} \sum_{j=2}^{j=i-1}{\left(a_{i,j} \sum_{k=1}^{k=j-1}{\left(a_{j,k} c_{k} \right)} \right)}\right) = \frac{\theta^{3}}{24}
        // \sum_{i=2}^{i=s}\left(b_{i} \sum_{j=1}^{j=i-1}{\left(a_{i,j} c_{j}^{2} \right)}\right) = \frac{\theta^{3}}{12}
        // \sum_{i=2}^{i=s}\left(b_{i} c_{i}\sum_{j=1}^{j=i-1}{\left(a_{i,j} c_{j} \right)}\right) = \frac{\theta^{3}}{8}
        // \sum_{i=1}^{i=s}\left(b_{i} c_{i}^{3}\right) = \frac{\theta^{3}}{4}
        // order 5 conditions
        // \sum_{i=4}^{i=s}\left(b_{i} \sum_{j=3}^{j=i-1}{\left(a_{i,j} \sum_{k=2}^{k=j-1}{\left(a_{j,k} \sum_{l=1}^{l=k-1}{\left(a_{k,l} c_{l} \right)} \right)} \right)}\right) = \frac{\theta^{4}}{120}
        // \sum_{i=3}^{i=s}\left(b_{i} \sum_{j=2}^{j=i-1}{\left(a_{i,j} \sum_{k=1}^{k=j-1}{\left(a_{j,k} c_{k}^{2} \right)} \right)}\right) = \frac{\theta^{4}}{60}
        // \sum_{i=3}^{i=s}\left(b_{i} \sum_{j=2}^{j=i-1}{\left(a_{i,j} c_{j}\sum_{k=1}^{k=j-1}{\left(a_{j,k} c_{k} \right)} \right)}\right) = \frac{\theta^{4}}{40}
        // \sum_{i=2}^{i=s}\left(b_{i} \sum_{j=1}^{j=i-1}{\left(a_{i,j} c_{j}^{3} \right)}\right) = \frac{\theta^{4}}{20}
        // \sum_{i=3}^{i=s}\left(b_{i} c_{i}\sum_{j=2}^{j=i-1}{\left(a_{i,j} \sum_{k=1}^{k=j-1}{\left(a_{j,k} c_{k} \right)} \right)}\right) = \frac{\theta^{4}}{30}
        // \sum_{i=2}^{i=s}\left(b_{i} c_{i}\sum_{j=1}^{j=i-1}{\left(a_{i,j} c_{j}^{2} \right)}\right) = \frac{\theta^{4}}{15}
        // \sum_{i=2}^{i=s}\left(b_{i} \left(\sum_{j=1}^{j=i-1}{\left(a_{i,j} c_{j} \right)} \right)^{2}\right) = \frac{\theta^{4}}{20}
        // \sum_{i=2}^{i=s}\left(b_{i} c_{i}^{2}\sum_{j=1}^{j=i-1}{\left(a_{i,j} c_{j} \right)}\right) = \frac{\theta^{4}}{10}
        // \sum_{i=1}^{i=s}\left(b_{i} c_{i}^{4}\right) = \frac{\theta^{4}}{5}

        // The a_{j,k} and c_{k} are given by the integrator Butcher arrays. What remains to solve
        // are the b_i for the interpolator. They are found by solving the above equations.
        // For a given interpolator, some equations are redundant, so in our case when we select
        // all equations from order 1 to 4, we still don't have enough independent equations
        // to solve from b_1 to b_7. We need to also select one equation from order 5. Here,
        // we selected the last equation. It appears this choice implied at least the last 3 equations
        // are fulfilled, but some of the former ones are not, so the resulting interpolator is order 5.
        // At the end, we get the b_i as polynomials in theta.

        final T coeffDot1 =  theta.multiply(theta.multiply(theta.multiply(theta.multiply(   21        ).add( -47          )).add(   36         )).add( -54     /   5.0)).add(1);
        final T coeffDot2 =  time.getField().getZero();
        final T coeffDot3 =  theta.multiply(theta.multiply(theta.multiply(theta.multiply(  112        ).add(-608    /  3.0)).add(  320   / 3.0 )).add(-208    /  15.0));
        final T coeffDot4 =  theta.multiply(theta.multiply(theta.multiply(theta.multiply( -567  /  5.0).add( 972    /  5.0)).add( -486   / 5.0 )).add( 324    /  25.0));
        final T coeffDot5 =  theta.multiply(theta.multiply(theta.multiply(theta.multiply(c5a.divide(5)).add(c5b.divide(15))).add(c5c.divide(30))).add(c5d.divide(150)));
        final T coeffDot6 =  theta.multiply(theta.multiply(theta.multiply(theta.multiply(c6a.divide(5)).add(c6b.divide(15))).add(c6c.divide(30))).add(c6d.divide(150)));
        final T coeffDot7 =  theta.multiply(theta.multiply(theta.multiply(                                             3.0 ).add(   -3         )).add(   3   /   5.0));
        final T[] interpolatedState;
        final T[] interpolatedDerivatives;

        if (getGlobalPreviousState() != null && theta.getReal() <= 0.5) {

            final T s         = thetaH;
            final T coeff1    = s.multiply(theta.multiply(theta.multiply(theta.multiply(theta.multiply(  21    /  5.0).add( -47    /  4.0)).add(   12         )).add( -27    /   5.0)).add(1));
            final T coeff2    = time.getField().getZero();
            final T coeff3    = s.multiply(theta.multiply(theta.multiply(theta.multiply(theta.multiply( 112    /  5.0).add(-152    /  3.0)).add(  320   / 9.0 )).add(-104    /  15.0)));
            final T coeff4    = s.multiply(theta.multiply(theta.multiply(theta.multiply(theta.multiply(-567    / 25.0).add( 243    /  5.0)).add( -162   / 5.0 )).add( 162    /  25.0)));
            final T coeff5    = s.multiply(theta.multiply(theta.multiply(theta.multiply(theta.multiply(c5a.divide(25)).add(c5b.divide(60))).add(c5c.divide(90))).add(c5d.divide(300))));
            final T coeff6    = s.multiply(theta.multiply(theta.multiply(theta.multiply(theta.multiply(c6a.divide(25)).add(c6b.divide(60))).add(c6c.divide(90))).add(c6d.divide(300))));
            final T coeff7    = s.multiply(theta.multiply(theta.multiply(theta.multiply(                                      3    /  4.0 ).add(   -1         )).add(   3    /  10.0)));
            interpolatedState       = previousStateLinearCombination(coeff1, coeff2, coeff3, coeff4, coeff5, coeff6, coeff7);
            interpolatedDerivatives = derivativeLinearCombination(coeffDot1, coeffDot2, coeffDot3, coeffDot4, coeffDot5, coeffDot6, coeffDot7);
        } else {

            final T s         = oneMinusThetaH;
            final T coeff1    = s.multiply(theta.multiply(theta.multiply(theta.multiply(theta.multiply( -21   /   5.0).add(   151  /  20.0)).add( -89   /   20.0)).add(  19 /  20.0)).add(- 1 / 20.0));
            final T coeff2    = time.getField().getZero();
            final T coeff3    = s.multiply(theta.multiply(theta.multiply(theta.multiply(theta.multiply(-112   /   5.0).add(   424  /  15.0)).add( -328  /   45.0)).add( -16 /  45.0)).add(-16 /  45.0));
            final T coeff4    = s.multiply(theta.multiply(theta.multiply(theta.multiply(theta.multiply( 567   /  25.0).add(  -648  /  25.0)).add(  162  /   25.0))));
            final T coeff5    = s.multiply(theta.multiply(theta.multiply(theta.multiply(theta.multiply(d5a.divide(25)).add(d5b.divide(300))).add(d5c.divide(900))).add( -49 / 180.0)).add(-49 / 180.0));
            final T coeff6    = s.multiply(theta.multiply(theta.multiply(theta.multiply(theta.multiply(d6a.divide(25)).add(d6b.divide(300))).add(d6c.divide(900))).add( -49 / 180.0)).add(-49 / 180.0));
            final T coeff7    = s.multiply(               theta.multiply(theta.multiply(theta.multiply(                        -3  /   4.0 ).add(   1   /    4.0)).add(  -1 /  20.0)).add( -1 /  20.0));
            interpolatedState       = currentStateLinearCombination(coeff1, coeff2, coeff3, coeff4, coeff5, coeff6, coeff7);
            interpolatedDerivatives = derivativeLinearCombination(coeffDot1, coeffDot2, coeffDot3, coeffDot4, coeffDot5, coeffDot6, coeffDot7);
        }

        return new FieldODEStateAndDerivative<T>(time, interpolatedState, interpolatedDerivatives);

    }

}
