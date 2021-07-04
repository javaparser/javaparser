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

import org.apache.commons.math3.analysis.UnivariateMatrixFunction;
import org.apache.commons.math3.exception.MathIllegalArgumentException;

/**
 * Extension of {@link UnivariateMatrixFunction} representing a univariate differentiable matrix function.
 *
 * @since 3.1
 */
public interface UnivariateDifferentiableMatrixFunction
    extends UnivariateMatrixFunction {

    /**
     * Compute the value for the function.
     * @param x the point for which the function value should be computed
     * @return the value
     * @exception MathIllegalArgumentException if {@code x} does not
     * satisfy the function's constraints (argument out of bound, or unsupported
     * derivative order for example)
     */
    DerivativeStructure[][] value(DerivativeStructure x) throws MathIllegalArgumentException;

}
