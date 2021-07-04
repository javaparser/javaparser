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

import org.apache.commons.math3.RealFieldElement;
import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.MaxCountExceededException;

/**
 * This interface allows users to add secondary differential equations to a primary
 * set of differential equations.
 * <p>
 * In some cases users may need to integrate some problem-specific equations along
 * with a primary set of differential equations. One example is optimal control where
 * adjoined parameters linked to the minimized Hamiltonian must be integrated.
 * </p>
 * <p>
 * This interface allows users to add such equations to a primary set of {@link
 * FirstOrderFieldDifferentialEquations first order differential equations}
 * thanks to the {@link FieldExpandableODE#addSecondaryEquations(FieldSecondaryEquations)}
 * method.
 * </p>
 * @see FirstOrderFieldDifferentialEquations
 * @see FieldExpandableODE
 * @param <T> the type of the field elements
 * @since 3.6
 */
public interface FieldSecondaryEquations<T extends RealFieldElement<T>> {

    /** Get the dimension of the secondary state parameters.
     * @return dimension of the secondary state parameters
     */
    int getDimension();

    /** Initialize equations at the start of an ODE integration.
     * <p>
     * This method is called once at the start of the integration. It
     * may be used by the equations to initialize some internal data
     * if needed.
     * </p>
     * @param t0 value of the independent <I>time</I> variable at integration start
     * @param primary0 array containing the value of the primary state vector at integration start
     * @param secondary0 array containing the value of the secondary state vector at integration start
     * @param finalTime target time for the integration
     */
    void init(T t0, T[] primary0, T[] secondary0, T finalTime);

    /** Compute the derivatives related to the secondary state parameters.
     * @param t current value of the independent <I>time</I> variable
     * @param primary array containing the current value of the primary state vector
     * @param primaryDot array containing the derivative of the primary state vector
     * @param secondary array containing the current value of the secondary state vector
     * @return derivative of the secondary state vector
     * @exception MaxCountExceededException if the number of functions evaluations is exceeded
     * @exception DimensionMismatchException if arrays dimensions do not match equations settings
     */
    T[] computeDerivatives(T t, T[] primary, T[] primaryDot, T[] secondary)
        throws MaxCountExceededException, DimensionMismatchException;

}
