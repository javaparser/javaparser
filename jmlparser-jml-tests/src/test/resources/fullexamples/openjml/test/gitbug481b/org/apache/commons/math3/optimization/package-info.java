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
 * <h2>All classes and sub-packages of this package are deprecated.</h2>
 * <h3>Please use their replacements, to be found under
 *  <ul>
 *   <li>{@link org.apache.commons.math3.optim}</li>
 *   <li>{@link org.apache.commons.math3.fitting}</li>
 *  </ul>
 * </h3>
 *
 * <p>
 * This package provides common interfaces for the optimization algorithms
 * provided in sub-packages. The main interfaces defines optimizers and convergence
 * checkers. The functions that are optimized by the algorithms provided by this
 * package and its sub-packages are a subset of the one defined in the <code>analysis</code>
 * package, namely the real and vector valued functions. These functions are called
 * objective function here. When the goal is to minimize, the functions are often called
 * cost function, this name is not used in this package.
 * </p>
 *
 * <p>
 * Optimizers are the algorithms that will either minimize or maximize, the objective function
 * by changing its input variables set until an optimal set is found. There are only four
 * interfaces defining the common behavior of optimizers, one for each supported type of objective
 * function:
 * <ul>
 *  <li>{@link org.apache.commons.math3.optimization.univariate.UnivariateOptimizer
 *      UnivariateOptimizer} for {@link org.apache.commons.math3.analysis.UnivariateFunction
 *      univariate real functions}</li>
 *  <li>{@link org.apache.commons.math3.optimization.MultivariateOptimizer
 *      MultivariateOptimizer} for {@link org.apache.commons.math3.analysis.MultivariateFunction
 *      multivariate real functions}</li>
 *  <li>{@link org.apache.commons.math3.optimization.MultivariateDifferentiableOptimizer
 *      MultivariateDifferentiableOptimizer} for {@link
 *      org.apache.commons.math3.analysis.differentiation.MultivariateDifferentiableFunction
 *      multivariate differentiable real functions}</li>
 *  <li>{@link org.apache.commons.math3.optimization.MultivariateDifferentiableVectorOptimizer
 *      MultivariateDifferentiableVectorOptimizer} for {@link
 *      org.apache.commons.math3.analysis.differentiation.MultivariateDifferentiableVectorFunction
 *      multivariate differentiable vectorial functions}</li>
 * </ul>
 * </p>
 *
 * <p>
 * Despite there are only four types of supported optimizers, it is possible to optimize a
 * transform a {@link org.apache.commons.math3.analysis.MultivariateVectorFunction
 * non-differentiable multivariate vectorial function} by converting it to a {@link
 * org.apache.commons.math3.analysis.MultivariateFunction non-differentiable multivariate
 * real function} thanks to the {@link
 * org.apache.commons.math3.optimization.LeastSquaresConverter LeastSquaresConverter} helper class.
 * The transformed function can be optimized using any implementation of the {@link
 * org.apache.commons.math3.optimization.MultivariateOptimizer MultivariateOptimizer} interface.
 * </p>
 *
 * <p>
 * For each of the four types of supported optimizers, there is a special implementation which
 * wraps a classical optimizer in order to add it a multi-start feature. This feature call the
 * underlying optimizer several times in sequence with different starting points and returns
 * the best optimum found or all optima if desired. This is a classical way to prevent being
 * trapped into a local extremum when looking for a global one.
 * </p>
 *
 */
package org.apache.commons.math3.optimization;
