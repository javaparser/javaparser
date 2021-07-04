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

package org.apache.commons.math3.analysis.function;

import java.util.Arrays;

import org.apache.commons.math3.analysis.FunctionUtils;
import org.apache.commons.math3.analysis.UnivariateFunction;
import org.apache.commons.math3.analysis.DifferentiableUnivariateFunction;
import org.apache.commons.math3.analysis.ParametricUnivariateFunction;
import org.apache.commons.math3.analysis.differentiation.DerivativeStructure;
import org.apache.commons.math3.analysis.differentiation.UnivariateDifferentiableFunction;
import org.apache.commons.math3.exception.NullArgumentException;
import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.util.FastMath;

/**
 * <a href="http://en.wikipedia.org/wiki/Sigmoid_function">
 *  Sigmoid</a> function.
 * It is the inverse of the {@link Logit logit} function.
 * A more flexible version, the generalised logistic, is implemented
 * by the {@link Logistic} class.
 *
 * @since 3.0
 */
public class Sigmoid implements UnivariateDifferentiableFunction, DifferentiableUnivariateFunction {
    /** Lower asymptote. */
    private final double lo;
    /** Higher asymptote. */
    private final double hi;

    /**
     * Usual sigmoid function, where the lower asymptote is 0 and the higher
     * asymptote is 1.
     */
    public Sigmoid() {
        this(0, 1);
    }

    /**
     * Sigmoid function.
     *
     * @param lo Lower asymptote.
     * @param hi Higher asymptote.
     */
    public Sigmoid(double lo,
                   double hi) {
        this.lo = lo;
        this.hi = hi;
    }

    /** {@inheritDoc}
     * @deprecated as of 3.1, replaced by {@link #value(DerivativeStructure)}
     */
    @Deprecated
    public UnivariateFunction derivative() {
        return FunctionUtils.toDifferentiableUnivariateFunction(this).derivative();
    }

    /** {@inheritDoc} */
    public double value(double x) {
        return value(x, lo, hi);
    }

    /**
     * Parametric function where the input array contains the parameters of
     * the {@link Sigmoid#Sigmoid(double,double) sigmoid function}, ordered
     * as follows:
     * <ul>
     *  <li>Lower asymptote</li>
     *  <li>Higher asymptote</li>
     * </ul>
     */
    public static class Parametric implements ParametricUnivariateFunction {
        /**
         * Computes the value of the sigmoid at {@code x}.
         *
         * @param x Value for which the function must be computed.
         * @param param Values of lower asymptote and higher asymptote.
         * @return the value of the function.
         * @throws NullArgumentException if {@code param} is {@code null}.
         * @throws DimensionMismatchException if the size of {@code param} is
         * not 2.
         */
        public double value(double x, double ... param)
            throws NullArgumentException,
                   DimensionMismatchException {
            validateParameters(param);
            return Sigmoid.value(x, param[0], param[1]);
        }

        /**
         * Computes the value of the gradient at {@code x}.
         * The components of the gradient vector are the partial
         * derivatives of the function with respect to each of the
         * <em>parameters</em> (lower asymptote and higher asymptote).
         *
         * @param x Value at which the gradient must be computed.
         * @param param Values for lower asymptote and higher asymptote.
         * @return the gradient vector at {@code x}.
         * @throws NullArgumentException if {@code param} is {@code null}.
         * @throws DimensionMismatchException if the size of {@code param} is
         * not 2.
         */
        public double[] gradient(double x, double ... param)
            throws NullArgumentException,
                   DimensionMismatchException {
            validateParameters(param);

            final double invExp1 = 1 / (1 + FastMath.exp(-x));

            return new double[] { 1 - invExp1, invExp1 };
        }

        /**
         * Validates parameters to ensure they are appropriate for the evaluation of
         * the {@link #value(double,double[])} and {@link #gradient(double,double[])}
         * methods.
         *
         * @param param Values for lower and higher asymptotes.
         * @throws NullArgumentException if {@code param} is {@code null}.
         * @throws DimensionMismatchException if the size of {@code param} is
         * not 2.
         */
        private void validateParameters(double[] param)
            throws NullArgumentException,
                   DimensionMismatchException {
            if (param == null) {
                throw new NullArgumentException();
            }
            if (param.length != 2) {
                throw new DimensionMismatchException(param.length, 2);
            }
        }
    }

    /**
     * @param x Value at which to compute the sigmoid.
     * @param lo Lower asymptote.
     * @param hi Higher asymptote.
     * @return the value of the sigmoid function at {@code x}.
     */
    private static double value(double x,
                                double lo,
                                double hi) {
        return lo + (hi - lo) / (1 + FastMath.exp(-x));
    }

    /** {@inheritDoc}
     * @since 3.1
     */
    public DerivativeStructure value(final DerivativeStructure t)
        throws DimensionMismatchException {

        double[] f = new double[t.getOrder() + 1];
        final double exp = FastMath.exp(-t.getValue());
        if (Double.isInfinite(exp)) {

            // special handling near lower boundary, to avoid NaN
            f[0] = lo;
            Arrays.fill(f, 1, f.length, 0.0);

        } else {

            // the nth order derivative of sigmoid has the form:
            // dn(sigmoid(x)/dxn = P_n(exp(-x)) / (1+exp(-x))^(n+1)
            // where P_n(t) is a degree n polynomial with normalized higher term
            // P_0(t) = 1, P_1(t) = t, P_2(t) = t^2 - t, P_3(t) = t^3 - 4 t^2 + t...
            // the general recurrence relation for P_n is:
            // P_n(x) = n t P_(n-1)(t) - t (1 + t) P_(n-1)'(t)
            final double[] p = new double[f.length];

            final double inv   = 1 / (1 + exp);
            double coeff = hi - lo;
            for (int n = 0; n < f.length; ++n) {

                // update and evaluate polynomial P_n(t)
                double v = 0;
                p[n] = 1;
                for (int k = n; k >= 0; --k) {
                    v = v * exp + p[k];
                    if (k > 1) {
                        p[k - 1] = (n - k + 2) * p[k - 2] - (k - 1) * p[k - 1];
                    } else {
                        p[0] = 0;
                    }
                }

                coeff *= inv;
                f[n]   = coeff * v;

            }

            // fix function value
            f[0] += lo;

        }

        return t.compose(f);

    }

}
