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
import org.apache.commons.math3.exception.NoBracketingException;
import org.apache.commons.math3.exception.NotStrictlyPositiveException;
import org.apache.commons.math3.exception.NullArgumentException;
import org.apache.commons.math3.exception.NumberIsTooLargeException;
import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.util.FastMath;

/**
 * Utility routines for {@link UnivariateSolver} objects.
 *
 */
public class UnivariateSolverUtils {
    /**
     * Class contains only static methods.
     */
    private UnivariateSolverUtils() {}

    /**
     * Convenience method to find a zero of a univariate real function.  A default
     * solver is used.
     *
     * @param function Function.
     * @param x0 Lower bound for the interval.
     * @param x1 Upper bound for the interval.
     * @return a value where the function is zero.
     * @throws NoBracketingException if the function has the same sign at the
     * endpoints.
     * @throws NullArgumentException if {@code function} is {@code null}.
     */
    public static double solve(UnivariateFunction function, double x0, double x1)
        throws NullArgumentException,
               NoBracketingException {
        if (function == null) {
            throw new NullArgumentException(LocalizedFormats.FUNCTION);
        }
        final UnivariateSolver solver = new BrentSolver();
        return solver.solve(Integer.MAX_VALUE, function, x0, x1);
    }

    /**
     * Convenience method to find a zero of a univariate real function.  A default
     * solver is used.
     *
     * @param function Function.
     * @param x0 Lower bound for the interval.
     * @param x1 Upper bound for the interval.
     * @param absoluteAccuracy Accuracy to be used by the solver.
     * @return a value where the function is zero.
     * @throws NoBracketingException if the function has the same sign at the
     * endpoints.
     * @throws NullArgumentException if {@code function} is {@code null}.
     */
    public static double solve(UnivariateFunction function,
                               double x0, double x1,
                               double absoluteAccuracy)
        throws NullArgumentException,
               NoBracketingException {
        if (function == null) {
            throw new NullArgumentException(LocalizedFormats.FUNCTION);
        }
        final UnivariateSolver solver = new BrentSolver(absoluteAccuracy);
        return solver.solve(Integer.MAX_VALUE, function, x0, x1);
    }

    /**
     * Force a root found by a non-bracketing solver to lie on a specified side,
     * as if the solver were a bracketing one.
     *
     * @param maxEval maximal number of new evaluations of the function
     * (evaluations already done for finding the root should have already been subtracted
     * from this number)
     * @param f function to solve
     * @param bracketing bracketing solver to use for shifting the root
     * @param baseRoot original root found by a previous non-bracketing solver
     * @param min minimal bound of the search interval
     * @param max maximal bound of the search interval
     * @param allowedSolution the kind of solutions that the root-finding algorithm may
     * accept as solutions.
     * @return a root approximation, on the specified side of the exact root
     * @throws NoBracketingException if the function has the same sign at the
     * endpoints.
     */
    public static double forceSide(final int maxEval, final UnivariateFunction f,
                                   final BracketedUnivariateSolver<UnivariateFunction> bracketing,
                                   final double baseRoot, final double min, final double max,
                                   final AllowedSolution allowedSolution)
        throws NoBracketingException {

        if (allowedSolution == AllowedSolution.ANY_SIDE) {
            // no further bracketing required
            return baseRoot;
        }

        // find a very small interval bracketing the root
        final double step = FastMath.max(bracketing.getAbsoluteAccuracy(),
                                         FastMath.abs(baseRoot * bracketing.getRelativeAccuracy()));
        double xLo        = FastMath.max(min, baseRoot - step);
        double fLo        = f.value(xLo);
        double xHi        = FastMath.min(max, baseRoot + step);
        double fHi        = f.value(xHi);
        int remainingEval = maxEval - 2;
        while (remainingEval > 0) {

            if ((fLo >= 0 && fHi <= 0) || (fLo <= 0 && fHi >= 0)) {
                // compute the root on the selected side
                return bracketing.solve(remainingEval, f, xLo, xHi, baseRoot, allowedSolution);
            }

            // try increasing the interval
            boolean changeLo = false;
            boolean changeHi = false;
            if (fLo < fHi) {
                // increasing function
                if (fLo >= 0) {
                    changeLo = true;
                } else {
                    changeHi = true;
                }
            } else if (fLo > fHi) {
                // decreasing function
                if (fLo <= 0) {
                    changeLo = true;
                } else {
                    changeHi = true;
                }
            } else {
                // unknown variation
                changeLo = true;
                changeHi = true;
            }

            // update the lower bound
            if (changeLo) {
                xLo = FastMath.max(min, xLo - step);
                fLo  = f.value(xLo);
                remainingEval--;
            }

            // update the higher bound
            if (changeHi) {
                xHi = FastMath.min(max, xHi + step);
                fHi  = f.value(xHi);
                remainingEval--;
            }

        }

        throw new NoBracketingException(LocalizedFormats.FAILED_BRACKETING,
                                        xLo, xHi, fLo, fHi,
                                        maxEval - remainingEval, maxEval, baseRoot,
                                        min, max);

    }

    /**
     * This method simply calls {@link #bracket(UnivariateFunction, double, double, double,
     * double, double, int) bracket(function, initial, lowerBound, upperBound, q, r, maximumIterations)}
     * with {@code q} and {@code r} set to 1.0 and {@code maximumIterations} set to {@code Integer.MAX_VALUE}.
     * <p>
     * <strong>Note: </strong> this method can take {@code Integer.MAX_VALUE}
     * iterations to throw a {@code ConvergenceException.}  Unless you are
     * confident that there is a root between {@code lowerBound} and
     * {@code upperBound} near {@code initial}, it is better to use
     * {@link #bracket(UnivariateFunction, double, double, double, double,double, int)
     * bracket(function, initial, lowerBound, upperBound, q, r, maximumIterations)},
     * explicitly specifying the maximum number of iterations.</p>
     *
     * @param function Function.
     * @param initial Initial midpoint of interval being expanded to
     * bracket a root.
     * @param lowerBound Lower bound (a is never lower than this value)
     * @param upperBound Upper bound (b never is greater than this
     * value).
     * @return a two-element array holding a and b.
     * @throws NoBracketingException if a root cannot be bracketted.
     * @throws NotStrictlyPositiveException if {@code maximumIterations <= 0}.
     * @throws NullArgumentException if {@code function} is {@code null}.
     */
    public static double[] bracket(UnivariateFunction function,
                                   double initial,
                                   double lowerBound, double upperBound)
        throws NullArgumentException,
               NotStrictlyPositiveException,
               NoBracketingException {
        return bracket(function, initial, lowerBound, upperBound, 1.0, 1.0, Integer.MAX_VALUE);
    }

     /**
     * This method simply calls {@link #bracket(UnivariateFunction, double, double, double,
     * double, double, int) bracket(function, initial, lowerBound, upperBound, q, r, maximumIterations)}
     * with {@code q} and {@code r} set to 1.0.
     * @param function Function.
     * @param initial Initial midpoint of interval being expanded to
     * bracket a root.
     * @param lowerBound Lower bound (a is never lower than this value).
     * @param upperBound Upper bound (b never is greater than this
     * value).
     * @param maximumIterations Maximum number of iterations to perform
     * @return a two element array holding a and b.
     * @throws NoBracketingException if the algorithm fails to find a and b
     * satisfying the desired conditions.
     * @throws NotStrictlyPositiveException if {@code maximumIterations <= 0}.
     * @throws NullArgumentException if {@code function} is {@code null}.
     */
    public static double[] bracket(UnivariateFunction function,
                                   double initial,
                                   double lowerBound, double upperBound,
                                   int maximumIterations)
        throws NullArgumentException,
               NotStrictlyPositiveException,
               NoBracketingException {
        return bracket(function, initial, lowerBound, upperBound, 1.0, 1.0, maximumIterations);
    }

    /**
     * This method attempts to find two values a and b satisfying <ul>
     * <li> {@code lowerBound <= a < initial < b <= upperBound} </li>
     * <li> {@code f(a) * f(b) <= 0} </li>
     * </ul>
     * If {@code f} is continuous on {@code [a,b]}, this means that {@code a}
     * and {@code b} bracket a root of {@code f}.
     * <p>
     * The algorithm checks the sign of \( f(l_k) \) and \( f(u_k) \) for increasing
     * values of k, where \( l_k = max(lower, initial - \delta_k) \),
     * \( u_k = min(upper, initial + \delta_k) \), using recurrence
     * \( \delta_{k+1} = r \delta_k + q, \delta_0 = 0\) and starting search with \( k=1 \).
     * The algorithm stops when one of the following happens: <ul>
     * <li> at least one positive and one negative value have been found --  success!</li>
     * <li> both endpoints have reached their respective limits -- NoBracketingException </li>
     * <li> {@code maximumIterations} iterations elapse -- NoBracketingException </li></ul>
     * <p>
     * If different signs are found at first iteration ({@code k=1}), then the returned
     * interval will be \( [a, b] = [l_1, u_1] \). If different signs are found at a later
     * iteration {@code k>1}, then the returned interval will be either
     * \( [a, b] = [l_{k+1}, l_{k}] \) or \( [a, b] = [u_{k}, u_{k+1}] \). A root solver called
     * with these parameters will therefore start with the smallest bracketing interval known
     * at this step.
     * </p>
     * <p>
     * Interval expansion rate is tuned by changing the recurrence parameters {@code r} and
     * {@code q}. When the multiplicative factor {@code r} is set to 1, the sequence is a
     * simple arithmetic sequence with linear increase. When the multiplicative factor {@code r}
     * is larger than 1, the sequence has an asymptotically exponential rate. Note than the
     * additive parameter {@code q} should never be set to zero, otherwise the interval would
     * degenerate to the single initial point for all values of {@code k}.
     * </p>
     * <p>
     * As a rule of thumb, when the location of the root is expected to be approximately known
     * within some error margin, {@code r} should be set to 1 and {@code q} should be set to the
     * order of magnitude of the error margin. When the location of the root is really a wild guess,
     * then {@code r} should be set to a value larger than 1 (typically 2 to double the interval
     * length at each iteration) and {@code q} should be set according to half the initial
     * search interval length.
     * </p>
     * <p>
     * As an example, if we consider the trivial function {@code f(x) = 1 - x} and use
     * {@code initial = 4}, {@code r = 1}, {@code q = 2}, the algorithm will compute
     * {@code f(4-2) = f(2) = -1} and {@code f(4+2) = f(6) = -5} for {@code k = 1}, then
     * {@code f(4-4) = f(0) = +1} and {@code f(4+4) = f(8) = -7} for {@code k = 2}. Then it will
     * return the interval {@code [0, 2]} as the smallest one known to be bracketing the root.
     * As shown by this example, the initial value (here {@code 4}) may lie outside of the returned
     * bracketing interval.
     * </p>
     * @param function function to check
     * @param initial Initial midpoint of interval being expanded to
     * bracket a root.
     * @param lowerBound Lower bound (a is never lower than this value).
     * @param upperBound Upper bound (b never is greater than this
     * value).
     * @param q additive offset used to compute bounds sequence (must be strictly positive)
     * @param r multiplicative factor used to compute bounds sequence
     * @param maximumIterations Maximum number of iterations to perform
     * @return a two element array holding the bracketing values.
     * @exception NoBracketingException if function cannot be bracketed in the search interval
     */
    public static double[] bracket(final UnivariateFunction function, final double initial,
                                   final double lowerBound, final double upperBound,
                                   final double q, final double r, final int maximumIterations)
        throws NoBracketingException {

        if (function == null) {
            throw new NullArgumentException(LocalizedFormats.FUNCTION);
        }
        if (q <= 0)  {
            throw new NotStrictlyPositiveException(q);
        }
        if (maximumIterations <= 0)  {
            throw new NotStrictlyPositiveException(LocalizedFormats.INVALID_MAX_ITERATIONS, maximumIterations);
        }
        verifySequence(lowerBound, initial, upperBound);

        // initialize the recurrence
        double a     = initial;
        double b     = initial;
        double fa    = Double.NaN;
        double fb    = Double.NaN;
        double delta = 0;

        for (int numIterations = 0;
             (numIterations < maximumIterations) && (a > lowerBound || b < upperBound);
             ++numIterations) {

            final double previousA  = a;
            final double previousFa = fa;
            final double previousB  = b;
            final double previousFb = fb;

            delta = r * delta + q;
            a     = FastMath.max(initial - delta, lowerBound);
            b     = FastMath.min(initial + delta, upperBound);
            fa    = function.value(a);
            fb    = function.value(b);

            if (numIterations == 0) {
                // at first iteration, we don't have a previous interval
                // we simply compare both sides of the initial interval
                if (fa * fb <= 0) {
                    // the first interval already brackets a root
                    return new double[] { a, b };
                }
            } else {
                // we have a previous interval with constant sign and expand it,
                // we expect sign changes to occur at boundaries
                if (fa * previousFa <= 0) {
                    // sign change detected at near lower bound
                    return new double[] { a, previousA };
                } else if (fb * previousFb <= 0) {
                    // sign change detected at near upper bound
                    return new double[] { previousB, b };
                }
            }

        }

        // no bracketing found
        throw new NoBracketingException(a, b, fa, fb);

    }

    /**
     * Compute the midpoint of two values.
     *
     * @param a first value.
     * @param b second value.
     * @return the midpoint.
     */
    public static double midpoint(double a, double b) {
        return (a + b) * 0.5;
    }

    /**
     * Check whether the interval bounds bracket a root. That is, if the
     * values at the endpoints are not equal to zero, then the function takes
     * opposite signs at the endpoints.
     *
     * @param function Function.
     * @param lower Lower endpoint.
     * @param upper Upper endpoint.
     * @return {@code true} if the function values have opposite signs at the
     * given points.
     * @throws NullArgumentException if {@code function} is {@code null}.
     */
    public static boolean isBracketing(UnivariateFunction function,
                                       final double lower,
                                       final double upper)
        throws NullArgumentException {
        if (function == null) {
            throw new NullArgumentException(LocalizedFormats.FUNCTION);
        }
        final double fLo = function.value(lower);
        final double fHi = function.value(upper);
        return (fLo >= 0 && fHi <= 0) || (fLo <= 0 && fHi >= 0);
    }

    /**
     * Check whether the arguments form a (strictly) increasing sequence.
     *
     * @param start First number.
     * @param mid Second number.
     * @param end Third number.
     * @return {@code true} if the arguments form an increasing sequence.
     */
    public static boolean isSequence(final double start,
                                     final double mid,
                                     final double end) {
        return (start < mid) && (mid < end);
    }

    /**
     * Check that the endpoints specify an interval.
     *
     * @param lower Lower endpoint.
     * @param upper Upper endpoint.
     * @throws NumberIsTooLargeException if {@code lower >= upper}.
     */
    public static void verifyInterval(final double lower,
                                      final double upper)
        throws NumberIsTooLargeException {
        if (lower >= upper) {
            throw new NumberIsTooLargeException(LocalizedFormats.ENDPOINTS_NOT_AN_INTERVAL,
                                                lower, upper, false);
        }
    }

    /**
     * Check that {@code lower < initial < upper}.
     *
     * @param lower Lower endpoint.
     * @param initial Initial value.
     * @param upper Upper endpoint.
     * @throws NumberIsTooLargeException if {@code lower >= initial} or
     * {@code initial >= upper}.
     */
    public static void verifySequence(final double lower,
                                      final double initial,
                                      final double upper)
        throws NumberIsTooLargeException {
        verifyInterval(lower, initial);
        verifyInterval(initial, upper);
    }

    /**
     * Check that the endpoints specify an interval and the end points
     * bracket a root.
     *
     * @param function Function.
     * @param lower Lower endpoint.
     * @param upper Upper endpoint.
     * @throws NoBracketingException if the function has the same sign at the
     * endpoints.
     * @throws NullArgumentException if {@code function} is {@code null}.
     */
    public static void verifyBracketing(UnivariateFunction function,
                                        final double lower,
                                        final double upper)
        throws NullArgumentException,
               NoBracketingException {
        if (function == null) {
            throw new NullArgumentException(LocalizedFormats.FUNCTION);
        }
        verifyInterval(lower, upper);
        if (!isBracketing(function, lower, upper)) {
            throw new NoBracketingException(lower, upper,
                                            function.value(lower),
                                            function.value(upper));
        }
    }
}
