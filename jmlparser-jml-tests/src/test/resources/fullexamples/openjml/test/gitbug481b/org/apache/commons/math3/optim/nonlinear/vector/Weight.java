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

import org.apache.commons.math3.optim.OptimizationData;
import org.apache.commons.math3.linear.RealMatrix;
import org.apache.commons.math3.linear.DiagonalMatrix;
import org.apache.commons.math3.linear.NonSquareMatrixException;

/**
 * Weight matrix of the residuals between model and observations.
 * <br/>
 * Immutable class.
 *
 * @since 3.1
 * @deprecated All classes and interfaces in this package are deprecated.
 * The optimizers that were provided here were moved to the
 * {@link org.apache.commons.math3.fitting.leastsquares} package
 * (cf. MATH-1008).
 */
@Deprecated
public class Weight implements OptimizationData {
    /** Weight matrix. */
    private final RealMatrix weightMatrix;

    /**
     * Creates a diagonal weight matrix.
     *
     * @param weight List of the values of the diagonal.
     */
    public Weight(double[] weight) {
        weightMatrix = new DiagonalMatrix(weight);
    }

    /**
     * @param weight Weight matrix.
     * @throws NonSquareMatrixException if the argument is not
     * a square matrix.
     */
    public Weight(RealMatrix weight) {
        if (weight.getColumnDimension() != weight.getRowDimension()) {
            throw new NonSquareMatrixException(weight.getColumnDimension(),
                                               weight.getRowDimension());
        }

        weightMatrix = weight.copy();
    }

    /**
     * Gets the initial guess.
     *
     * @return the initial guess.
     */
    public RealMatrix getWeight() {
        return weightMatrix.copy();
    }
}
