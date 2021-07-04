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
package org.apache.commons.math3.analysis.integration;

import org.apache.commons.math3.analysis.UnivariateFunction;
import org.apache.commons.math3.exception.MathIllegalArgumentException;
import org.apache.commons.math3.exception.MaxCountExceededException;
import org.apache.commons.math3.exception.NullArgumentException;
import org.apache.commons.math3.exception.TooManyEvaluationsException;

/**
 * Interface for univariate real integration algorithms.
 *
 * @since 1.2
 */
public interface UnivariateIntegrator {

    /**
     * Get the relative accuracy.
     *
     * @return the accuracy
     */
    double getRelativeAccuracy();

    /**
     * Get the absolute accuracy.
     *
     * @return the accuracy
     */
    double getAbsoluteAccuracy();

    /**
     * Get the min limit for the number of iterations.
     *
     * @return the actual min limit
     */
    int getMinimalIterationCount();

    /**
     * Get the upper limit for the number of iterations.
     *
     * @return the actual upper limit
     */
    int getMaximalIterationCount();

    /**
     * Integrate the function in the given interval.
     *
     * @param maxEval Maximum number of evaluations.
     * @param f the integrand function
     * @param min the lower bound for the interval
     * @param max the upper bound for the interval
     * @return the value of integral
     * @throws TooManyEvaluationsException if the maximum number of function
     * evaluations is exceeded
     * @throws MaxCountExceededException if the maximum iteration count is exceeded
     * or the integrator detects convergence problems otherwise
     * @throws MathIllegalArgumentException if {@code min > max} or the endpoints do not
     * satisfy the requirements specified by the integrator
     * @throws NullArgumentException if {@code f} is {@code null}.
     */
    double integrate(int maxEval, UnivariateFunction f, double min,
                     double max)
        throws TooManyEvaluationsException, MaxCountExceededException,
               MathIllegalArgumentException, NullArgumentException;

    /**
     * Get the number of function evaluations of the last run of the integrator.
     *
     * @return number of function evaluations
     */
    int getEvaluations();

    /**
     * Get the number of iterations of the last run of the integrator.
     *
     * @return number of iterations
     */
    int getIterations();

}
