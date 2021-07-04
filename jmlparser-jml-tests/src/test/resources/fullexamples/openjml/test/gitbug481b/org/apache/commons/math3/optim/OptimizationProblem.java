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
package org.apache.commons.math3.optim;

import org.apache.commons.math3.util.Incrementor;

/**
 * Common settings for all optimization problems. Includes divergence and convergence
 * criteria.
 *
 * @param <PAIR> The type of value the {@link #getConvergenceChecker() convergence
 *               checker} will operate on. It should include the value of the model
 *               function and point where it was evaluated.
 * @since 3.3
 */
public interface OptimizationProblem<PAIR> {
    /**
     * Get a independent Incrementor that counts up to the maximum number of evaluations
     * and then throws an exception.
     *
     * @return a counter for the evaluations.
     */
    Incrementor getEvaluationCounter();

    /**
     * Get a independent Incrementor that counts up to the maximum number of iterations
     * and then throws an exception.
     *
     * @return a counter for the evaluations.
     */
    Incrementor getIterationCounter();

    /**
     * Gets the convergence checker.
     *
     * @return the object used to check for convergence.
     */
    ConvergenceChecker<PAIR> getConvergenceChecker();
}
