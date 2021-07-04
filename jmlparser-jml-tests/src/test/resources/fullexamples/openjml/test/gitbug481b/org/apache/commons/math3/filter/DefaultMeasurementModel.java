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
package org.apache.commons.math3.filter;

import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.NoDataException;
import org.apache.commons.math3.exception.NullArgumentException;
import org.apache.commons.math3.linear.Array2DRowRealMatrix;
import org.apache.commons.math3.linear.RealMatrix;

/**
 * Default implementation of a {@link MeasurementModel} for the use with a {@link KalmanFilter}.
 *
 * @since 3.0
 */
public class DefaultMeasurementModel implements MeasurementModel {

    /**
     * The measurement matrix, used to associate the measurement vector to the
     * internal state estimation vector.
     */
    private RealMatrix measurementMatrix;

    /**
     * The measurement noise covariance matrix.
     */
    private RealMatrix measurementNoise;

    /**
     * Create a new {@link MeasurementModel}, taking double arrays as input parameters for the
     * respective measurement matrix and noise.
     *
     * @param measMatrix
     *            the measurement matrix
     * @param measNoise
     *            the measurement noise matrix
     * @throws NullArgumentException
     *             if any of the input matrices is {@code null}
     * @throws NoDataException
     *             if any row / column dimension of the input matrices is zero
     * @throws DimensionMismatchException
     *             if any of the input matrices is non-rectangular
     */
    public DefaultMeasurementModel(final double[][] measMatrix, final double[][] measNoise)
            throws NullArgumentException, NoDataException, DimensionMismatchException {
        this(new Array2DRowRealMatrix(measMatrix), new Array2DRowRealMatrix(measNoise));
    }

    /**
     * Create a new {@link MeasurementModel}, taking {@link RealMatrix} objects
     * as input parameters for the respective measurement matrix and noise.
     *
     * @param measMatrix the measurement matrix
     * @param measNoise the measurement noise matrix
     */
    public DefaultMeasurementModel(final RealMatrix measMatrix, final RealMatrix measNoise) {
        this.measurementMatrix = measMatrix;
        this.measurementNoise = measNoise;
    }

    /** {@inheritDoc} */
    public RealMatrix getMeasurementMatrix() {
        return measurementMatrix;
    }

    /** {@inheritDoc} */
    public RealMatrix getMeasurementNoise() {
        return measurementNoise;
    }
}
