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
package org.apache.commons.math3.ode;

import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.MaxCountExceededException;

/** Interface expanding {@link FirstOrderDifferentialEquations first order
 *  differential equations} in order to compute exactly the main state jacobian
 *  matrix for {@link JacobianMatrices partial derivatives equations}.
 *
 * @since 3.0
 */
public interface MainStateJacobianProvider extends FirstOrderDifferentialEquations {

    /** Compute the jacobian matrix of ODE with respect to main state.
     * @param t current value of the independent <I>time</I> variable
     * @param y array containing the current value of the main state vector
     * @param yDot array containing the current value of the time derivative of the main state vector
     * @param dFdY placeholder array where to put the jacobian matrix of the ODE w.r.t. the main state vector
     * @exception MaxCountExceededException if the number of functions evaluations is exceeded
     * @exception DimensionMismatchException if arrays dimensions do not match equations settings
     */
    void computeMainStateJacobian(double t, double[] y, double[] yDot, double[][] dFdY)
        throws MaxCountExceededException, DimensionMismatchException;

}
