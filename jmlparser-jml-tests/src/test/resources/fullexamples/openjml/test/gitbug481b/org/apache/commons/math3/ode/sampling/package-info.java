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
 * This package provides classes to handle sampling steps during
 * Ordinary Differential Equations integration.
 * </p>
 *
 * <p>
 * In addition to computing the evolution of the state vector at some grid points, all
 * ODE integrators also build up interpolation models of this evolution <em>inside</em> the
 * last computed step. If users are interested in these interpolators, they can register a
 * {@link org.apache.commons.math3.ode.sampling.StepHandler StepHandler} instance using the
 * {@link org.apache.commons.math3.ode.FirstOrderIntegrator#addStepHandler addStepHandler}
 * method which is supported by all integrators. The integrator will call this instance
 * at the end of each accepted step and provide it the interpolator. The user can do
 * whatever he wants with this interpolator, which computes both the state and its
 * time-derivative. A typical use of step handler is to provide some output to monitor
 * the integration process.
 * </p>
 *
 * <p>
 * In a sense, this is a kind of Inversion Of Control: rather than having the master
 * application driving the slave integrator by providing the target end value for
 * the free variable, we get a master integrator scheduling the free variable
 * evolution and calling the slave application callbacks that were registered at
 * configuration time.
 * </p>
 *
 * <p>
 * Since some integrators may use variable step size, the generic {@link
 * org.apache.commons.math3.ode.sampling.StepHandler StepHandler} interface can be called
 * either at regular or irregular rate. This interface allows to navigate to any location
 * within the last computed step, thanks to the provided {@link
 * org.apache.commons.math3.ode.sampling.StepInterpolator StepInterpolator} object.
 * If regular output is desired (for example in order to write an ephemeris file), then
 * the simpler {@link org.apache.commons.math3.ode.sampling.FixedStepHandler FixedStepHandler}
 * interface can be used. Objects implementing this interface should be wrapped within a
 * {@link org.apache.commons.math3.ode.sampling.StepNormalizer StepNormalizer} instance
 * in order to be registered to the integrator.
 * </p>
 *
 *
 */
package org.apache.commons.math3.ode.sampling;
