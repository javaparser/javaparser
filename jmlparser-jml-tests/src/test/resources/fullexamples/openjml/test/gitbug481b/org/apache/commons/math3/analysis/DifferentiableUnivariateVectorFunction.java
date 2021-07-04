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
package org.apache.commons.math3.analysis;

/**
 * Extension of {@link UnivariateVectorFunction} representing a differentiable univariate vectorial function.
 *
 * @since 2.0
 * @deprecated as of 3.1 replaced by {@link org.apache.commons.math3.analysis.differentiation.UnivariateDifferentiableVectorFunction}
 */
@Deprecated
public interface DifferentiableUnivariateVectorFunction
    extends UnivariateVectorFunction {

    /**
     * Returns the derivative of the function
     *
     * @return  the derivative function
     */
    UnivariateVectorFunction derivative();

}
