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
package org.apache.commons.math3.dfp;


import org.apache.commons.math3.analysis.RealFieldUnivariateFunction;
import org.apache.commons.math3.analysis.solvers.AllowedSolution;
import org.apache.commons.math3.analysis.solvers.FieldBracketingNthOrderBrentSolver;
import org.apache.commons.math3.exception.NoBracketingException;
import org.apache.commons.math3.exception.NullArgumentException;
import org.apache.commons.math3.exception.NumberIsTooSmallException;
import org.apache.commons.math3.util.MathUtils;

/**
 * This class implements a modification of the <a
 * href="http://mathworld.wolfram.com/BrentsMethod.html"> Brent algorithm</a>.
 * <p>
 * The changes with respect to the original Brent algorithm are:
 * <ul>
 *   <li>the returned value is chosen in the current interval according
 *   to user specified {@link AllowedSolution},</li>
 *   <li>the maximal order for the invert polynomial root search is
 *   user-specified instead of being invert quadratic only</li>
 * </ul>
 * </p>
 * The given interval must bracket the root.
 * @deprecated as of 3.6 replaced with {@link FieldBracketingNthOrderBrentSolver}
 */
@Deprecated
public class BracketingNthOrderBrentSolverDFP extends FieldBracketingNthOrderBrentSolver<Dfp> {

    /**
     * Construct a solver.
     *
     * @param relativeAccuracy Relative accuracy.
     * @param absoluteAccuracy Absolute accuracy.
     * @param functionValueAccuracy Function value accuracy.
     * @param maximalOrder maximal order.
     * @exception NumberIsTooSmallException if maximal order is lower than 2
     */
    public BracketingNthOrderBrentSolverDFP(final Dfp relativeAccuracy,
                                            final Dfp absoluteAccuracy,
                                            final Dfp functionValueAccuracy,
                                            final int maximalOrder)
        throws NumberIsTooSmallException {
        super(relativeAccuracy, absoluteAccuracy, functionValueAccuracy, maximalOrder);
    }

    /**
     * Get the absolute accuracy.
     * @return absolute accuracy
     */
    @Override
    public Dfp getAbsoluteAccuracy() {
        return super.getAbsoluteAccuracy();
    }

    /**
     * Get the relative accuracy.
     * @return relative accuracy
     */
    @Override
    public Dfp getRelativeAccuracy() {
        return super.getRelativeAccuracy();
    }

    /**
     * Get the function accuracy.
     * @return function accuracy
     */
    @Override
    public Dfp getFunctionValueAccuracy() {
        return super.getFunctionValueAccuracy();
    }

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
     * @return a value where the function is zero.
     * @exception NullArgumentException if f is null.
     * @exception NoBracketingException if root cannot be bracketed
     */
    public Dfp solve(final int maxEval, final UnivariateDfpFunction f,
                     final Dfp min, final Dfp max, final AllowedSolution allowedSolution)
        throws NullArgumentException, NoBracketingException {
        return solve(maxEval, f, min, max, min.add(max).divide(2), allowedSolution);
    }

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
     * @return a value where the function is zero.
     * @exception NullArgumentException if f is null.
     * @exception NoBracketingException if root cannot be bracketed
     */
    public Dfp solve(final int maxEval, final UnivariateDfpFunction f,
                     final Dfp min, final Dfp max, final Dfp startValue,
                     final AllowedSolution allowedSolution)
        throws NullArgumentException, NoBracketingException {

        // checks
        MathUtils.checkNotNull(f);

        // wrap the function
        RealFieldUnivariateFunction<Dfp> fieldF = new RealFieldUnivariateFunction<Dfp>() {

            /** {@inheritDoc} */
            public Dfp value(final Dfp x) {
                return f.value(x);
            }
        };

        // delegate to general field solver
        return solve(maxEval, fieldF, min, max, startValue, allowedSolution);

    }

}
