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
 * This package provides classes to solve Ordinary Differential Equations problems.
 * </p>
 *
 * <p>
 * This package solves Initial Value Problems of the form
 * <code>y'=f(t,y)</code> with <code>t<sub>0</sub></code> and
 * <code>y(t<sub>0</sub>)=y<sub>0</sub></code> known. The provided
 * integrators compute an estimate of <code>y(t)</code> from
 * <code>t=t<sub>0</sub></code> to <code>t=t<sub>1</sub></code>.
 * It is also possible to get thederivatives with respect to the initial state
 * <code>dy(t)/dy(t<sub>0</sub>)</code> or the derivatives with
 * respect to some ODE parameters <code>dy(t)/dp</code>.
 * </p>
 *
 * <p>
 * All integrators provide dense output. This means that besides
 * computing the state vector at discrete times, they also provide a
 * cheap mean to get the state between the time steps. They do so through
 * classes extending the {@link
 * org.apache.commons.math3.ode.sampling.StepInterpolator StepInterpolator}
 * abstract class, which are made available to the user at the end of
 * each step.
 * </p>
 *
 * <p>
 * All integrators handle multiple discrete events detection based on switching
 * functions. This means that the integrator can be driven by user specified
 * discrete events. The steps are shortened as needed to ensure the events occur
 * at step boundaries (even if the integrator is a fixed-step
 * integrator). When the events are triggered, integration can be stopped
 * (this is called a G-stop facility), the state vector can be changed,
 * or integration can simply go on. The latter case is useful to handle
 * discontinuities in the differential equations gracefully and get
 * accurate dense output even close to the discontinuity.
 * </p>
 *
 * <p>
 * The user should describe his problem in his own classes
 * (<code>UserProblem</code> in the diagram below) which should implement
 * the {@link org.apache.commons.math3.ode.FirstOrderDifferentialEquations
 * FirstOrderDifferentialEquations} interface. Then he should pass it to
 * the integrator he prefers among all the classes that implement the
 * {@link org.apache.commons.math3.ode.FirstOrderIntegrator
 * FirstOrderIntegrator} interface.
 * </p>
 *
 * <p>
 * The solution of the integration problem is provided by two means. The
 * first one is aimed towards simple use: the state vector at the end of
 * the integration process is copied in the <code>y</code> array of the
 * {@link org.apache.commons.math3.ode.FirstOrderIntegrator#integrate
 * FirstOrderIntegrator.integrate} method. The second one should be used
 * when more in-depth information is needed throughout the integration
 * process. The user can register an object implementing the {@link
 * org.apache.commons.math3.ode.sampling.StepHandler StepHandler} interface or a
 * {@link org.apache.commons.math3.ode.sampling.StepNormalizer StepNormalizer}
 * object wrapping a user-specified object implementing the {@link
 * org.apache.commons.math3.ode.sampling.FixedStepHandler FixedStepHandler}
 * interface into the integrator before calling the {@link
 * org.apache.commons.math3.ode.FirstOrderIntegrator#integrate
 * FirstOrderIntegrator.integrate} method. The user object will be called
 * appropriately during the integration process, allowing the user to
 * process intermediate results. The default step handler does nothing.
 * </p>
 *
 * <p>
 * {@link org.apache.commons.math3.ode.ContinuousOutputModel
 * ContinuousOutputModel} is a special-purpose step handler that is able
 * to store all steps and to provide transparent access to any
 * intermediate result once the integration is over. An important feature
 * of this class is that it implements the <code>Serializable</code>
 * interface. This means that a complete continuous model of the
 * integrated function throughout the integration range can be serialized
 * and reused later (if stored into a persistent medium like a filesystem
 * or a database) or elsewhere (if sent to another application). Only the
 * result of the integration is stored, there is no reference to the
 * integrated problem by itself.
 * </p>
 *
 * <p>
 * Other default implementations of the {@link
 * org.apache.commons.math3.ode.sampling.StepHandler StepHandler} interface are
 * available for general needs ({@link
 * org.apache.commons.math3.ode.sampling.DummyStepHandler DummyStepHandler}, {@link
 * org.apache.commons.math3.ode.sampling.StepNormalizer StepNormalizer}) and custom
 * implementations can be developed for specific needs. As an example,
 * if an application is to be completely driven by the integration
 * process, then most of the application code will be run inside a step
 * handler specific to this application.
 * </p>
 *
 * <p>
 * Some integrators (the simple ones) use fixed steps that are set at
 * creation time. The more efficient integrators use variable steps that
 * are handled internally in order to control the integration error with
 * respect to a specified accuracy (these integrators extend the {@link
 * org.apache.commons.math3.ode.nonstiff.AdaptiveStepsizeIntegrator
 * AdaptiveStepsizeIntegrator} abstract class). In this case, the step
 * handler which is called after each successful step shows up the
 * variable stepsize. The {@link
 * org.apache.commons.math3.ode.sampling.StepNormalizer StepNormalizer} class can
 * be used to convert the variable stepsize into a fixed stepsize that
 * can be handled by classes implementing the {@link
 * org.apache.commons.math3.ode.sampling.FixedStepHandler FixedStepHandler}
 * interface. Adaptive stepsize integrators can automatically compute the
 * initial stepsize by themselves, however the user can specify it if he
 * prefers to retain full control over the integration or if the
 * automatic guess is wrong.
 * </p>
 *
 * <p>
 * <table border="1" align="center">
 * <tr BGCOLOR="#CCCCFF"><td colspan=2><font size="+2">Fixed Step Integrators</font></td></tr>
 * <tr BGCOLOR="#EEEEFF"><font size="+1"><td>Name</td><td>Order</td></font></tr>
 * <tr><td>{@link org.apache.commons.math3.ode.nonstiff.EulerIntegrator Euler}</td><td>1</td></tr>
 * <tr><td>{@link org.apache.commons.math3.ode.nonstiff.MidpointIntegrator Midpoint}</td><td>2</td></tr>
 * <tr><td>{@link org.apache.commons.math3.ode.nonstiff.ClassicalRungeKuttaIntegrator Classical Runge-Kutta}</td><td>4</td></tr>
 * <tr><td>{@link org.apache.commons.math3.ode.nonstiff.GillIntegrator Gill}</td><td>4</td></tr>
 * <tr><td>{@link org.apache.commons.math3.ode.nonstiff.ThreeEighthesIntegrator 3/8}</td><td>4</td></tr>
 * <tr><td>{@link org.apache.commons.math3.ode.nonstiff.LutherIntegrator Luther}</td><td>6</td></tr>
 * </table>
 * </p>
 *
 * <table border="1" align="center">
 * <tr BGCOLOR="#CCCCFF"><td colspan=3><font size="+2">Adaptive Stepsize Integrators</font></td></tr>
 * <tr BGCOLOR="#EEEEFF"><font size="+1"><td>Name</td><td>Integration Order</td><td>Error Estimation Order</td></font></tr>
 * <tr><td>{@link org.apache.commons.math3.ode.nonstiff.HighamHall54Integrator Higham and Hall}</td><td>5</td><td>4</td></tr>
 * <tr><td>{@link org.apache.commons.math3.ode.nonstiff.DormandPrince54Integrator Dormand-Prince 5(4)}</td><td>5</td><td>4</td></tr>
 * <tr><td>{@link org.apache.commons.math3.ode.nonstiff.DormandPrince853Integrator Dormand-Prince 8(5,3)}</td><td>8</td><td>5 and 3</td></tr>
 * <tr><td>{@link org.apache.commons.math3.ode.nonstiff.GraggBulirschStoerIntegrator Gragg-Bulirsch-Stoer}</td><td>variable (up to 18 by default)</td><td>variable</td></tr>
 * <tr><td>{@link org.apache.commons.math3.ode.nonstiff.AdamsBashforthIntegrator Adams-Bashforth}</td><td>variable</td><td>variable</td></tr>
 * <tr><td>{@link org.apache.commons.math3.ode.nonstiff.AdamsMoultonIntegrator Adams-Moulton}</td><td>variable</td><td>variable</td></tr>
 * </table>
 * </p>
 *
 * <p>
 * In the table above, the {@link org.apache.commons.math3.ode.nonstiff.AdamsBashforthIntegrator
 * Adams-Bashforth} and {@link org.apache.commons.math3.ode.nonstiff.AdamsMoultonIntegrator
 * Adams-Moulton} integrators appear as variable-step ones. This is an experimental extension
 * to the classical algorithms using the Nordsieck vector representation.
 * </p>
 *
 *
 */
package org.apache.commons.math3.ode;
