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

import org.apache.commons.math3.ode.sampling.StepInterpolator;
import org.apache.commons.math3.util.FastMath;

/**
 * This class represents an interpolator over the last step during an
 * ODE integration for the 6th order Luther integrator.
 *
 * <p>This interpolator computes dense output inside the last
 * step computed. The interpolation equation is consistent with the
 * integration scheme.</p>
 *
 * @see LutherIntegrator
 * @since 3.3
 */

class LutherStepInterpolator extends RungeKuttaStepInterpolator {

    /** Serializable version identifier */
    private static final long serialVersionUID = 20140416L;

    /** Square root. */
    private static final double Q = FastMath.sqrt(21);

    /** Simple constructor.
     * This constructor builds an instance that is not usable yet, the
     * {@link
     * org.apache.commons.math3.ode.sampling.AbstractStepInterpolator#reinitialize}
     * method should be called before using the instance in order to
     * initialize the internal arrays. This constructor is used only
     * in order to delay the initialization in some cases. The {@link
     * RungeKuttaIntegrator} class uses the prototyping design pattern
     * to create the step interpolators by cloning an uninitialized model
     * and later initializing the copy.
     */
    // CHECKSTYLE: stop RedundantModifier
    // the public modifier here is needed for serialization
    public LutherStepInterpolator() {
    }
    // CHECKSTYLE: resume RedundantModifier

    /** Copy constructor.
     * @param interpolator interpolator to copy from. The copy is a deep
     * copy: its arrays are separated from the original arrays of the
     * instance
     */
    LutherStepInterpolator(final LutherStepInterpolator interpolator) {
        super(interpolator);
    }

    /** {@inheritDoc} */
    @Override
    protected StepInterpolator doCopy() {
        return new LutherStepInterpolator(this);
    }


    /** {@inheritDoc} */
    @Override
    protected void computeInterpolatedStateAndDerivatives(final double theta,
                                                          final double oneMinusThetaH) {

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

        final double coeffDot1 =  1 + theta * ( -54            /   5.0 + theta * (   36                   + theta * ( -47                   + theta *   21)));
        final double coeffDot2 =  0;
        final double coeffDot3 =      theta * (-208            /  15.0 + theta * (  320            / 3.0  + theta * (-608            /  3.0 + theta *  112)));
        final double coeffDot4 =      theta * ( 324            /  25.0 + theta * ( -486            / 5.0  + theta * ( 972            /  5.0 + theta * -567           /  5.0)));
        final double coeffDot5 =      theta * ((833 + 343 * Q) / 150.0 + theta * ((-637 - 357 * Q) / 30.0 + theta * ((392 + 287 * Q) / 15.0 + theta * (-49 - 49 * Q) /  5.0)));
        final double coeffDot6 =      theta * ((833 - 343 * Q) / 150.0 + theta * ((-637 + 357 * Q) / 30.0 + theta * ((392 - 287 * Q) / 15.0 + theta * (-49 + 49 * Q) /  5.0)));
        final double coeffDot7 =      theta * (   3            /   5.0 + theta * (   -3                   + theta *     3));

        if ((previousState != null) && (theta <= 0.5)) {

            final double coeff1    =  1 + theta * ( -27            /   5.0 + theta * (   12                   + theta * ( -47            /  4.0 + theta *   21           /  5.0)));
            final double coeff2    =  0;
            final double coeff3    =      theta * (-104            /  15.0 + theta * (  320            / 9.0  + theta * (-152            /  3.0 + theta *  112           /  5.0)));
            final double coeff4    =      theta * ( 162            /  25.0 + theta * ( -162            / 5.0  + theta * ( 243            /  5.0 + theta * -567           / 25.0)));
            final double coeff5    =      theta * ((833 + 343 * Q) / 300.0 + theta * ((-637 - 357 * Q) / 90.0 + theta * ((392 + 287 * Q) / 60.0 + theta * (-49 - 49 * Q) / 25.0)));
            final double coeff6    =      theta * ((833 - 343 * Q) / 300.0 + theta * ((-637 + 357 * Q) / 90.0 + theta * ((392 - 287 * Q) / 60.0 + theta * (-49 + 49 * Q) / 25.0)));
            final double coeff7    =      theta * (   3            /  10.0 + theta * (   -1                   + theta * (   3            /  4.0)));
            for (int i = 0; i < interpolatedState.length; ++i) {
                final double yDot1 = yDotK[0][i];
                final double yDot2 = yDotK[1][i];
                final double yDot3 = yDotK[2][i];
                final double yDot4 = yDotK[3][i];
                final double yDot5 = yDotK[4][i];
                final double yDot6 = yDotK[5][i];
                final double yDot7 = yDotK[6][i];
                interpolatedState[i] = previousState[i] +
                        theta * h * (coeff1 * yDot1 + coeff2 * yDot2 + coeff3 * yDot3 +
                                     coeff4 * yDot4 + coeff5 * yDot5 + coeff6 * yDot6 + coeff7 * yDot7);
                interpolatedDerivatives[i] = coeffDot1 * yDot1 + coeffDot2 * yDot2 + coeffDot3 * yDot3 +
                        coeffDot4 * yDot4 + coeffDot5 * yDot5 + coeffDot6 * yDot6 + coeffDot7 * yDot7;
            }
        } else {

            final double coeff1    =  -1 /  20.0 + theta * (  19            /  20.0 + theta * (  -89             /  20.0  + theta * (   151            /  20.0 + theta *  -21           /   5.0)));
            final double coeff2    =  0;
            final double coeff3    = -16 /  45.0 + theta * ( -16            /  45.0 + theta * ( -328             /  45.0  + theta * (   424            /  15.0 + theta * -112           /   5.0)));
            final double coeff4    =               theta * (                          theta * (  162             /  25.0  + theta * (  -648            /  25.0 + theta *  567           /  25.0)));
            final double coeff5    = -49 / 180.0 + theta * ( -49            / 180.0 + theta * ((2254 + 1029 * Q) / 900.0  + theta * ((-1372 - 847 * Q) / 300.0 + theta * ( 49 + 49 * Q) /  25.0)));
            final double coeff6    = -49 / 180.0 + theta * ( -49            / 180.0 + theta * ((2254 - 1029 * Q) / 900.0  + theta * ((-1372 + 847 * Q) / 300.0 + theta * ( 49 - 49 * Q) /  25.0)));
            final double coeff7    =  -1 /  20.0 + theta * (  -1            /  20.0 + theta * (    1             /   4.0  + theta * (    -3            /   4.0)));
            for (int i = 0; i < interpolatedState.length; ++i) {
                final double yDot1 = yDotK[0][i];
                final double yDot2 = yDotK[1][i];
                final double yDot3 = yDotK[2][i];
                final double yDot4 = yDotK[3][i];
                final double yDot5 = yDotK[4][i];
                final double yDot6 = yDotK[5][i];
                final double yDot7 = yDotK[6][i];
                interpolatedState[i] = currentState[i] +
                        oneMinusThetaH * (coeff1 * yDot1 + coeff2 * yDot2 + coeff3 * yDot3 +
                                          coeff4 * yDot4 + coeff5 * yDot5 + coeff6 * yDot6 + coeff7 * yDot7);
                interpolatedDerivatives[i] = coeffDot1 * yDot1 + coeffDot2 * yDot2 + coeffDot3 * yDot3 +
                        coeffDot4 * yDot4 + coeffDot5 * yDot5 + coeffDot6 * yDot6 + coeffDot7 * yDot7;
            }
        }

    }

}
