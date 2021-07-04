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
package org.apache.commons.math3.optim.nonlinear.vector;

import org.apache.commons.math3.analysis.MultivariateMatrixFunction;
import org.apache.commons.math3.optim.ConvergenceChecker;
import org.apache.commons.math3.optim.OptimizationData;
import org.apache.commons.math3.optim.PointVectorValuePair;
import org.apache.commons.math3.exception.TooManyEvaluationsException;
import org.apache.commons.math3.exception.DimensionMismatchException;

/**
 * Base class for implementing optimizers for multivariate vector
 * differentiable functions.
 * It contains boiler-plate code for dealing with Jacobian evaluation.
 * It assumes that the rows of the Jacobian matrix iterate on the model
 * functions while the columns iterate on the parameters; thus, the numbers
 * of rows is equal to the dimension of the {@link Target} while the
 * number of columns is equal to the dimension of the
 * {@link org.apache.commons.math3.optim.InitialGuess InitialGuess}.
 *
 * @since 3.1
 * @deprecated All classes and interfaces in this package are deprecated.
 * The optimizers that were provided here were moved to the
 * {@link org.apache.commons.math3.fitting.leastsquares} package
 * (cf. MATH-1008).
 */
@Deprecated
public abstract class JacobianMultivariateVectorOptimizer
    extends MultivariateVectorOptimizer {
    /**
     * Jacobian of the model function.
     */
    private MultivariateMatrixFunction jacobian;

    /**
     * @param checker Convergence checker.
     */
    protected JacobianMultivariateVectorOptimizer(ConvergenceChecker<PointVectorValuePair> checker) {
        super(checker);
    }

    /**
     * Computes the Jacobian matrix.
     *
     * @param params Point at which the Jacobian must be evaluated.
     * @return the Jacobian at the specified point.
     */
    protected double[][] computeJacobian(final double[] params) {
        return jacobian.value(params);
    }

    /**
     * {@inheritDoc}
     *
     * @param optData Optimization data. In addition to those documented in
     * {@link MultivariateVectorOptimizer#optimize(OptimizationData...)}
     * MultivariateOptimizer}, this method will register the following data:
     * <ul>
     *  <li>{@link ModelFunctionJacobian}</li>
     * </ul>
     * @return {@inheritDoc}
     * @throws TooManyEvaluationsException if the maximal number of
     * evaluations is exceeded.
     * @throws DimensionMismatchException if the initial guess, target, and weight
     * arguments have inconsistent dimensions.
     */
    @Override
    public PointVectorValuePair optimize(OptimizationData... optData)
        throws TooManyEvaluationsException,
               DimensionMismatchException {
        // Set up base class and perform computation.
        return super.optimize(optData);
    }

    /**
     * Scans the list of (required and optional) optimization data that
     * characterize the problem.
     *
     * @param optData Optimization data.
     * The following data will be looked for:
     * <ul>
     *  <li>{@link ModelFunctionJacobian}</li>
     * </ul>
     */
    @Override
    protected void parseOptimizationData(OptimizationData... optData) {
        // Allow base class to register its own data.
        super.parseOptimizationData(optData);

        // The existing values (as set by the previous call) are reused if
        // not provided in the argument list.
        for (OptimizationData data : optData) {
            if (data instanceof ModelFunctionJacobian) {
                jacobian = ((ModelFunctionJacobian) data).getModelFunctionJacobian();
                // If more data must be parsed, this statement _must_ be
                // changed to "continue".
                break;
            }
        }
    }
}
