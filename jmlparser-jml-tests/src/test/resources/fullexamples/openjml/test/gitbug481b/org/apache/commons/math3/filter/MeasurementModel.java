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

import org.apache.commons.math3.linear.RealMatrix;

/**
 * Defines the measurement model for the use with a {@link KalmanFilter}.
 *
 * @since 3.0
 */
public interface MeasurementModel {
    /**
     * Returns the measurement matrix.
     *
     * @return the measurement matrix
     */
    RealMatrix getMeasurementMatrix();

    /**
     * Returns the measurement noise matrix. This method is called by the {@link KalmanFilter} every
     * correction step, so implementations of this interface may return a modified measurement noise
     * depending on the current iteration step.
     *
     * @return the measurement noise matrix
     * @see KalmanFilter#correct(double[])
     * @see KalmanFilter#correct(org.apache.commons.math3.linear.RealVector)
     */
    RealMatrix getMeasurementNoise();
}
