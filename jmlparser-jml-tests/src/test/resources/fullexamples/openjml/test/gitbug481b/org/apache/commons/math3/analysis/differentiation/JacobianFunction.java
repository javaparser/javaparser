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

import org.apache.commons.math3.analysis.MultivariateMatrixFunction;

/** Class representing the Jacobian of a multivariate vector function.
 * <p>
 * The rows iterate on the model functions while the columns iterate on the parameters; thus,
 * the numbers of rows is equal to the dimension of the underlying function vector
 * value and the number of columns is equal to the number of free parameters of
 * the underlying function.
 * </p>
 * @since 3.1
 */
public class JacobianFunction implements MultivariateMatrixFunction {

    /** Underlying vector-valued function. */
    private final MultivariateDifferentiableVectorFunction f;

    /** Simple constructor.
     * @param f underlying vector-valued function
     */
    public JacobianFunction(final MultivariateDifferentiableVectorFunction f) {
        this.f = f;
    }

    /** {@inheritDoc} */
    public double[][] value(double[] point) {

        // set up parameters
        final DerivativeStructure[] dsX = new DerivativeStructure[point.length];
        for (int i = 0; i < point.length; ++i) {
            dsX[i] = new DerivativeStructure(point.length, 1, i, point[i]);
        }

        // compute the derivatives
        final DerivativeStructure[] dsY = f.value(dsX);

        // extract the Jacobian
        final double[][] y = new double[dsY.length][point.length];
        final int[] orders = new int[point.length];
        for (int i = 0; i < dsY.length; ++i) {
            for (int j = 0; j < point.length; ++j) {
                orders[j] = 1;
                y[i][j] = dsY[i].getPartialDerivative(orders);
                orders[j] = 0;
            }
        }

        return y;

    }

}
