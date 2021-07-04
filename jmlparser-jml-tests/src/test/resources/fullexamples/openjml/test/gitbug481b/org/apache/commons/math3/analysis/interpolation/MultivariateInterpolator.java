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
package org.apache.commons.math3.analysis.interpolation;

import org.apache.commons.math3.analysis.MultivariateFunction;
import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.MathIllegalArgumentException;
import org.apache.commons.math3.exception.NoDataException;
import org.apache.commons.math3.exception.NullArgumentException;

/**
 * Interface representing a univariate real interpolating function.
 *
 * @since 2.1
 */
public interface MultivariateInterpolator {

    /**
     * Computes an interpolating function for the data set.
     *
     * @param xval the arguments for the interpolation points.
     * {@code xval[i][0]} is the first component of interpolation point
     * {@code i}, {@code xval[i][1]} is the second component, and so on
     * until {@code xval[i][d-1]}, the last component of that interpolation
     * point (where {@code d} is thus the dimension of the space).
     * @param yval the values for the interpolation points
     * @return a function which interpolates the data set
     * @throws MathIllegalArgumentException if the arguments violate assumptions
     * made by the interpolation algorithm.
     * @throws DimensionMismatchException when the array dimensions are not consistent.
     * @throws NoDataException if an array has zero-length.
     * @throws NullArgumentException if the arguments are {@code null}.
     */
    MultivariateFunction interpolate(double[][] xval, double[] yval)
        throws MathIllegalArgumentException, DimensionMismatchException,
               NoDataException, NullArgumentException;
}
