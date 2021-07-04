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


/**
 * This class implements the classical fourth order Runge-Kutta
 * integrator for Ordinary Differential Equations (it is the most
 * often used Runge-Kutta method).
 *
 * <p>This method is an explicit Runge-Kutta method, its Butcher-array
 * is the following one :
 * <pre>
 *    0  |  0    0    0    0
 *   1/2 | 1/2   0    0    0
 *   1/2 |  0   1/2   0    0
 *    1  |  0    0    1    0
 *       |--------------------
 *       | 1/6  1/3  1/3  1/6
 * </pre>
 * </p>
 *
 * @see EulerIntegrator
 * @see GillIntegrator
 * @see MidpointIntegrator
 * @see ThreeEighthesIntegrator
 * @see LutherIntegrator
 * @since 1.2
 */

public class ClassicalRungeKuttaIntegrator extends RungeKuttaIntegrator {

  /** Time steps Butcher array. */
  private static final double[] STATIC_C = {
    1.0 / 2.0, 1.0 / 2.0, 1.0
  };

  /** Internal weights Butcher array. */
  private static final double[][] STATIC_A = {
    { 1.0 / 2.0 },
    { 0.0, 1.0 / 2.0 },
    { 0.0, 0.0, 1.0 }
  };

  /** Propagation weights Butcher array. */
  private static final double[] STATIC_B = {
    1.0 / 6.0, 1.0 / 3.0, 1.0 / 3.0, 1.0 / 6.0
  };

  /** Simple constructor.
   * Build a fourth-order Runge-Kutta integrator with the given
   * step.
   * @param step integration step
   */
  public ClassicalRungeKuttaIntegrator(final double step) {
    super("classical Runge-Kutta", STATIC_C, STATIC_A, STATIC_B,
          new ClassicalRungeKuttaStepInterpolator(), step);
  }

}
