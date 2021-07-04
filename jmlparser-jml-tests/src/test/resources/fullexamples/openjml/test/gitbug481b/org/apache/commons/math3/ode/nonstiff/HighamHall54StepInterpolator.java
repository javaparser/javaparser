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

/**
 * This class represents an interpolator over the last step during an
 * ODE integration for the 5(4) Higham and Hall integrator.
 *
 * @see HighamHall54Integrator
 *
 * @since 1.2
 */

class HighamHall54StepInterpolator
  extends RungeKuttaStepInterpolator {

  /** Serializable version identifier */
  private static final long serialVersionUID = 20111120L;

  /** Simple constructor.
   * This constructor builds an instance that is not usable yet, the
   * {@link
   * org.apache.commons.math3.ode.sampling.AbstractStepInterpolator#reinitialize}
   * method should be called before using the instance in order to
   * initialize the internal arrays. This constructor is used only
   * in order to delay the initialization in some cases. The {@link
   * EmbeddedRungeKuttaIntegrator} uses the prototyping design pattern
   * to create the step interpolators by cloning an uninitialized model
   * and later initializing the copy.
   */
  // CHECKSTYLE: stop RedundantModifier
  // the public modifier here is needed for serialization
  public HighamHall54StepInterpolator() {
    super();
  }
  // CHECKSTYLE: resume RedundantModifier

  /** Copy constructor.
   * @param interpolator interpolator to copy from. The copy is a deep
   * copy: its arrays are separated from the original arrays of the
   * instance
   */
  HighamHall54StepInterpolator(final HighamHall54StepInterpolator interpolator) {
    super(interpolator);
  }

  /** {@inheritDoc} */
  @Override
  protected StepInterpolator doCopy() {
    return new HighamHall54StepInterpolator(this);
  }


  /** {@inheritDoc} */
  @Override
  protected void computeInterpolatedStateAndDerivatives(final double theta,
                                          final double oneMinusThetaH) {

    final double bDot0 = 1 + theta * (-15.0/2.0 + theta * (16.0 - 10.0 * theta));
    final double bDot2 = theta * (459.0/16.0 + theta * (-729.0/8.0 + 135.0/2.0 * theta));
    final double bDot3 = theta * (-44.0 + theta * (152.0 - 120.0 * theta));
    final double bDot4 = theta * (375.0/16.0 + theta * (-625.0/8.0 + 125.0/2.0 * theta));
    final double bDot5 = theta * 5.0/8.0 * (2 * theta - 1);

    if ((previousState != null) && (theta <= 0.5)) {
        final double hTheta = h * theta;
        final double b0 = hTheta * (1.0 + theta * (-15.0/4.0  + theta * (16.0/3.0 - 5.0/2.0 * theta)));
        final double b2 = hTheta * (      theta * (459.0/32.0 + theta * (-243.0/8.0 + theta * 135.0/8.0)));
        final double b3 = hTheta * (      theta * (-22.0      + theta * (152.0/3.0  + theta * -30.0)));
        final double b4 = hTheta * (      theta * (375.0/32.0 + theta * (-625.0/24.0 + theta * 125.0/8.0)));
        final double b5 = hTheta * (      theta * (-5.0/16.0  + theta *  5.0/12.0));
        for (int i = 0; i < interpolatedState.length; ++i) {
            final double yDot0 = yDotK[0][i];
            final double yDot2 = yDotK[2][i];
            final double yDot3 = yDotK[3][i];
            final double yDot4 = yDotK[4][i];
            final double yDot5 = yDotK[5][i];
            interpolatedState[i] =
                    previousState[i] + b0 * yDot0 + b2 * yDot2 + b3 * yDot3 + b4 * yDot4 + b5 * yDot5;
            interpolatedDerivatives[i] =
                    bDot0 * yDot0 + bDot2 * yDot2 + bDot3 * yDot3 + bDot4 * yDot4 + bDot5 * yDot5;
        }
    } else {
        final double theta2 = theta * theta;
        final double b0 = h * (-1.0/12.0 + theta * (1.0 + theta * (-15.0/4.0 + theta * (16.0/3.0 + theta * -5.0/2.0))));
        final double b2 = h * (-27.0/32.0 + theta2 * (459.0/32.0 + theta * (-243.0/8.0 + theta * 135.0/8.0)));
        final double b3 = h * (4.0/3.0 + theta2 * (-22.0 + theta * (152.0/3.0  + theta * -30.0)));
        final double b4 = h * (-125.0/96.0 + theta2 * (375.0/32.0 + theta * (-625.0/24.0 + theta * 125.0/8.0)));
        final double b5 = h * (-5.0/48.0 + theta2 * (-5.0/16.0 + theta * 5.0/12.0));
        for (int i = 0; i < interpolatedState.length; ++i) {
            final double yDot0 = yDotK[0][i];
            final double yDot2 = yDotK[2][i];
            final double yDot3 = yDotK[3][i];
            final double yDot4 = yDotK[4][i];
            final double yDot5 = yDotK[5][i];
            interpolatedState[i] =
                    currentState[i] + b0 * yDot0 + b2 * yDot2 + b3 * yDot3 + b4 * yDot4 + b5 * yDot5;
            interpolatedDerivatives[i] =
                    bDot0 * yDot0 + bDot2 * yDot2 + bDot3 * yDot3 + bDot4 * yDot4 + bDot5 * yDot5;
        }
    }

  }

}
