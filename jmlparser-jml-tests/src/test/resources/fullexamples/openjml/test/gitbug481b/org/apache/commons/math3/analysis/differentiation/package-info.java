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
 *   This package holds the main interfaces and basic building block classes
 *   dealing with differentiation.
 *   The core class is {@link org.apache.commons.math3.analysis.differentiation.DerivativeStructure
 *   DerivativeStructure} which holds the value and the differentials of a function. This class
 *   handles some arbitrary number of free parameters and arbitrary differentiation order. It is used
 *   both as the input and the output type for the {@link
 *   org.apache.commons.math3.analysis.differentiation.UnivariateDifferentiableFunction
 *   UnivariateDifferentiableFunction} interface. Any differentiable function should implement this
 *   interface.
 * </p>
 * <p>
 *   The {@link org.apache.commons.math3.analysis.differentiation.UnivariateFunctionDifferentiator
 *   UnivariateFunctionDifferentiator} interface defines a way to differentiate a simple {@link
 *   org.apache.commons.math3.analysis.UnivariateFunction UnivariateFunction} and get a {@link
 *   org.apache.commons.math3.analysis.differentiation.UnivariateDifferentiableFunction
 *   UnivariateDifferentiableFunction}.
 * </p>
 * <p>
 *   Similar interfaces also exist for multivariate functions and for vector or matrix valued functions.
 * </p>
 *
 */
package org.apache.commons.math3.analysis.differentiation;
