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

import org.apache.commons.math3.RealFieldElement;

/** This interface represents an integrator  based on Butcher arrays.
 * @see RungeKuttaFieldIntegrator
 * @see EmbeddedRungeKuttaFieldIntegrator
 * @param <T> the type of the field elements
 * @since 3.6
 */

public interface FieldButcherArrayProvider<T extends RealFieldElement<T>> {

    /** Get the time steps from Butcher array (without the first zero).
     * @return time steps from Butcher array (without the first zero
     */
    T[] getC();

    /** Get the internal weights from Butcher array (without the first empty row).
     * @return internal weights from Butcher array (without the first empty row)
     */
    T[][] getA();

    /** Get the external weights for the high order method from Butcher array.
     * @return external weights for the high order method from Butcher array
     */
    T[] getB();

}
