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
/**
 *
 * <p>
 * This package provides classes to handle discrete events occurring during
 * Ordinary Differential Equations integration.
 * </p>
 *
 * <p>
 * Discrete events detection is based on switching functions. The user provides
 * a simple {@link org.apache.commons.math3.ode.events.EventHandler#g g(t, y)}
 * function depending on the current time and state. The integrator will monitor
 * the value of the function throughout integration range and will trigger the
 * event when its sign changes. The magnitude of the value is almost irrelevant,
 * it should however be continuous (but not necessarily smooth) for the sake of
 * root finding. The steps are shortened as needed to ensure the events occur
 * at step boundaries (even if the integrator is a fixed-step integrator).
 * </p>
 *
 * <p>
 * When an event is triggered, several different options are available:
 * </p>
 * <ul>
 *  <li>integration can be stopped (this is called a G-stop facility),</li>
 *  <li>the state vector or the derivatives can be changed,</li>
 *  <li>or integration can simply go on.</li>
 * </ul>
 *
 * <p>
 * The first case, G-stop, is the most common one. A typical use case is when an
 * ODE must be solved up to some target state is reached, with a known value of
 * the state but an unknown occurrence time. As an example, if we want to monitor
 * a chemical reaction up to some predefined concentration for the first substance,
 * we can use the following switching function setting:
 * <pre>
 *  public double g(double t, double[] y) {
 *    return y[0] - targetConcentration;
 *  }
 *
 *  public int eventOccurred(double t, double[] y) {
 *    return STOP;
 *  }
 * </pre>
 * </p>
 *
 * <p>
 * The second case, change state vector or derivatives is encountered when dealing
 * with discontinuous dynamical models. A typical case would be the motion of a
 * spacecraft when thrusters are fired for orbital maneuvers. The acceleration is
 * smooth as long as no maneuver are performed, depending only on gravity, drag,
 * third body attraction, radiation pressure. Firing a thruster introduces a
 * discontinuity that must be handled appropriately by the integrator. In such a case,
 * we would use a switching function setting similar to this:
 * <pre>
 *  public double g(double t, double[] y) {
 *    return (t - tManeuverStart) &lowast; (t - tManeuverStop);
 *  }
 *
 *  public int eventOccurred(double t, double[] y) {
 *    return RESET_DERIVATIVES;
 *  }
 * </pre>
 * </p>
 *
 * <p>
 * The third case is useful mainly for monitoring purposes, a simple example is:
 * <pre>
 *  public double g(double t, double[] y) {
 *    return y[0] - y[1];
 *  }
 *
 *  public int eventOccurred(double t, double[] y) {
 *    logger.log("y0(t) and y1(t) curves cross at t = " + t);
 *    return CONTINUE;
 *  }
 * </pre>
 * </p>
 *
 *
 */
package org.apache.commons.math3.ode.events;
