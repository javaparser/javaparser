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
package org.apache.commons.math3.fitting.leastsquares;

/**
 * An algorithm that can be applied to a non-linear least squares problem.
 *
 * @since 3.3
 */
public interface LeastSquaresOptimizer {

    /**
     * Solve the non-linear least squares problem.
     *
     *
     * @param leastSquaresProblem the problem definition, including model function and
     *                            convergence criteria.
     * @return The optimum.
     */
    Optimum optimize(LeastSquaresProblem leastSquaresProblem);

    /**
     * The optimum found by the optimizer. This object contains the point, its value, and
     * some metadata.
     */
    //TODO Solution?
    interface Optimum extends LeastSquaresProblem.Evaluation {

        /**
         * Get the number of times the model was evaluated in order to produce this
         * optimum.
         *
         * @return the number of model (objective) function evaluations
         */
        int getEvaluations();

        /**
         * Get the number of times the algorithm iterated in order to produce this
         * optimum. In general least squares it is common to have one {@link
         * #getEvaluations() evaluation} per iterations.
         *
         * @return the number of iterations
         */
        int getIterations();

    }

}
