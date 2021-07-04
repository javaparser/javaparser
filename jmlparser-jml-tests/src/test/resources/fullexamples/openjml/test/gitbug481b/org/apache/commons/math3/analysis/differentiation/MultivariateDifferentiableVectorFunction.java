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

package org.apache.commons.math3.analysis.differentiation;

import org.apache.commons.math3.analysis.MultivariateVectorFunction;
import org.apache.commons.math3.exception.MathIllegalArgumentException;


/**
 * Extension of {@link MultivariateVectorFunction} representing a
 * multivariate differentiable vectorial function.
 * @since 3.1
 */
public interface MultivariateDifferentiableVectorFunction
    extends MultivariateVectorFunction {

    /**
     * Compute the value for the function at the given point.
     * @param point point at which the function must be evaluated
     * @return function value for the given point
     * @exception MathIllegalArgumentException if {@code point} does not
     * satisfy the function's constraints (wrong dimension, argument out of bound,
     * or unsupported derivative order for example)
     */
    DerivativeStructure[] value(DerivativeStructure[] point)
        throws MathIllegalArgumentException;

}
