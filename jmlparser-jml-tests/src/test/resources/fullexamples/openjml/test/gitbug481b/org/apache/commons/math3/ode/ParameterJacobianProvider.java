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

/** Interface to compute exactly Jacobian matrix for some parameter
 *  when computing {@link JacobianMatrices partial derivatives equations}.
 *
 * @since 3.0
 */
public interface ParameterJacobianProvider extends Parameterizable {

    /** Compute the Jacobian matrix of ODE with respect to one parameter.
     * <p>If the parameter does not belong to the collection returned by
     * {@link #getParametersNames()}, the Jacobian will be set to 0,
     * but no errors will be triggered.</p>
     * @param t current value of the independent <I>time</I> variable
     * @param y array containing the current value of the main state vector
     * @param yDot array containing the current value of the time derivative
     * of the main state vector
     * @param paramName name of the parameter to consider
     * @param dFdP placeholder array where to put the Jacobian matrix of the
     * ODE with respect to the parameter
     * @exception MaxCountExceededException if the number of functions evaluations is exceeded
     * @exception DimensionMismatchException if arrays dimensions do not match equations settings
     * @exception UnknownParameterException if the parameter is not supported
     */
    void computeParameterJacobian(double t, double[] y, double[] yDot,
                                  String paramName, double[] dFdP)
        throws DimensionMismatchException, MaxCountExceededException, UnknownParameterException;

}
