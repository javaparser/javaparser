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

import org.apache.commons.math3.analysis.UnivariateFunction;
import org.apache.commons.math3.exception.DimensionMismatchException;

/** Interface for univariate functions derivatives.
 * <p>This interface represents a simple function which computes
 * both the value and the first derivative of a mathematical function.
 * The derivative is computed with respect to the input variable.</p>
 * @see UnivariateDifferentiableFunction
 * @see UnivariateFunctionDifferentiator
 * @since 3.1
 */
public interface UnivariateDifferentiableFunction extends UnivariateFunction {

    /** Simple mathematical function.
     * <p>{@link UnivariateDifferentiableFunction} classes compute both the
     * value and the first derivative of the function.</p>
     * @param t function input value
     * @return function result
     * @exception DimensionMismatchException if t is inconsistent with the
     * function's free parameters or order
     */
    DerivativeStructure value(DerivativeStructure t)
        throws DimensionMismatchException;

}
