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

package org.apache.commons.math3.analysis.solvers;

import org.apache.commons.math3.analysis.UnivariateFunction;

/** Interface for {@link UnivariateSolver (univariate real) root-finding
 * algorithms} that maintain a bracketed solution. There are several advantages
 * to having such root-finding algorithms:
 * <ul>
 *  <li>The bracketed solution guarantees that the root is kept within the
 *      interval. As such, these algorithms generally also guarantee
 *      convergence.</li>
 *  <li>The bracketed solution means that we have the opportunity to only
 *      return roots that are greater than or equal to the actual root, or
 *      are less than or equal to the actual root. That is, we can control
 *      whether under-approximations and over-approximations are
 *      {@link AllowedSolution allowed solutions}. Other root-finding
 *      algorithms can usually only guarantee that the solution (the root that
 *      was found) is around the actual root.</li>
 * </ul>
 *
 * <p>For backwards compatibility, all root-finding algorithms must have
 * {@link AllowedSolution#ANY_SIDE ANY_SIDE} as default for the allowed
 * solutions.</p>
 * @param <FUNC> Type of function to solve.
 *
 * @see AllowedSolution
 * @since 3.0
 */
public interface BracketedUnivariateSolver<FUNC extends UnivariateFunction>
    extends BaseUnivariateSolver<FUNC> {

    /**
     * Solve for a zero in the given interval.
     * A solver may require that the interval brackets a single zero root.
     * Solvers that do require bracketing should be able to handle the case
     * where one of the endpoints is itself a root.
     *
     * @param maxEval Maximum number of evaluations.
     * @param f Function to solve.
     * @param min Lower bound for the interval.
     * @param max Upper bound for the interval.
     * @param allowedSolution The kind of solutions that the root-finding algorithm may
     * accept as solutions.
     * @return A value where the function is zero.
     * @throws org.apache.commons.math3.exception.MathIllegalArgumentException
     * if the arguments do not satisfy the requirements specified by the solver.
     * @throws org.apache.commons.math3.exception.TooManyEvaluationsException if
     * the allowed number of evaluations is exceeded.
     */
    double solve(int maxEval, FUNC f, double min, double max,
                 AllowedSolution allowedSolution);

    /**
     * Solve for a zero in the given interval, start at {@code startValue}.
     * A solver may require that the interval brackets a single zero root.
     * Solvers that do require bracketing should be able to handle the case
     * where one of the endpoints is itself a root.
     *
     * @param maxEval Maximum number of evaluations.
     * @param f Function to solve.
     * @param min Lower bound for the interval.
     * @param max Upper bound for the interval.
     * @param startValue Start value to use.
     * @param allowedSolution The kind of solutions that the root-finding algorithm may
     * accept as solutions.
     * @return A value where the function is zero.
     * @throws org.apache.commons.math3.exception.MathIllegalArgumentException
     * if the arguments do not satisfy the requirements specified by the solver.
     * @throws org.apache.commons.math3.exception.TooManyEvaluationsException if
     * the allowed number of evaluations is exceeded.
     */
    double solve(int maxEval, FUNC f, double min, double max, double startValue,
                 AllowedSolution allowedSolution);

}
