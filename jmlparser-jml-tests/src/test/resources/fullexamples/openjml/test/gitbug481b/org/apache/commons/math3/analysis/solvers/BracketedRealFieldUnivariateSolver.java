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

import org.apache.commons.math3.RealFieldElement;
import org.apache.commons.math3.analysis.RealFieldUnivariateFunction;

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
 *
 * @see AllowedSolution
 * @param <T> the type of the field elements
 * @since 3.6
 */
public interface BracketedRealFieldUnivariateSolver<T extends RealFieldElement<T>> {

    /**
     * Get the maximum number of function evaluations.
     *
     * @return the maximum number of function evaluations.
     */
    int getMaxEvaluations();

    /**
     * Get the number of evaluations of the objective function.
     * The number of evaluations corresponds to the last call to the
     * {@code optimize} method. It is 0 if the method has not been
     * called yet.
     *
     * @return the number of evaluations of the objective function.
     */
    int getEvaluations();

    /**
     * Get the absolute accuracy of the solver.  Solutions returned by the
     * solver should be accurate to this tolerance, i.e., if &epsilon; is the
     * absolute accuracy of the solver and {@code v} is a value returned by
     * one of the {@code solve} methods, then a root of the function should
     * exist somewhere in the interval ({@code v} - &epsilon;, {@code v} + &epsilon;).
     *
     * @return the absolute accuracy.
     */
    T getAbsoluteAccuracy();

    /**
     * Get the relative accuracy of the solver.  The contract for relative
     * accuracy is the same as {@link #getAbsoluteAccuracy()}, but using
     * relative, rather than absolute error.  If &rho; is the relative accuracy
     * configured for a solver and {@code v} is a value returned, then a root
     * of the function should exist somewhere in the interval
     * ({@code v} - &rho; {@code v}, {@code v} + &rho; {@code v}).
     *
     * @return the relative accuracy.
     */
    T getRelativeAccuracy();

    /**
     * Get the function value accuracy of the solver.  If {@code v} is
     * a value returned by the solver for a function {@code f},
     * then by contract, {@code |f(v)|} should be less than or equal to
     * the function value accuracy configured for the solver.
     *
     * @return the function value accuracy.
     */
    T getFunctionValueAccuracy();

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
    T solve(int maxEval, RealFieldUnivariateFunction<T> f, T min, T max,
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
    T solve(int maxEval, RealFieldUnivariateFunction<T> f, T min, T max, T startValue,
            AllowedSolution allowedSolution);

}
