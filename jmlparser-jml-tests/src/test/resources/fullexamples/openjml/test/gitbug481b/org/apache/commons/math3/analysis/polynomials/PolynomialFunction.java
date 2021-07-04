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
package org.apache.commons.math3.analysis.polynomials;

import java.io.Serializable;
import java.util.Arrays;

import org.apache.commons.math3.analysis.DifferentiableUnivariateFunction;
import org.apache.commons.math3.analysis.ParametricUnivariateFunction;
import org.apache.commons.math3.analysis.UnivariateFunction;
import org.apache.commons.math3.analysis.differentiation.DerivativeStructure;
import org.apache.commons.math3.analysis.differentiation.UnivariateDifferentiableFunction;
import org.apache.commons.math3.exception.NoDataException;
import org.apache.commons.math3.exception.NullArgumentException;
import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.util.FastMath;
import org.apache.commons.math3.util.MathUtils;

/**
 * Immutable representation of a real polynomial function with real coefficients.
 * <p>
 * <a href="http://mathworld.wolfram.com/HornersMethod.html">Horner's Method</a>
 * is used to evaluate the function.</p>
 *
 */
public class PolynomialFunction implements UnivariateDifferentiableFunction, DifferentiableUnivariateFunction, Serializable {
    /**
     * Serialization identifier
     */
    private static final long serialVersionUID = -7726511984200295583L;
    /**
     * The coefficients of the polynomial, ordered by degree -- i.e.,
     * coefficients[0] is the constant term and coefficients[n] is the
     * coefficient of x^n where n is the degree of the polynomial.
     */
    private final double coefficients[];

    /**
     * Construct a polynomial with the given coefficients.  The first element
     * of the coefficients array is the constant term.  Higher degree
     * coefficients follow in sequence.  The degree of the resulting polynomial
     * is the index of the last non-null element of the array, or 0 if all elements
     * are null.
     * <p>
     * The constructor makes a copy of the input array and assigns the copy to
     * the coefficients property.</p>
     *
     * @param c Polynomial coefficients.
     * @throws NullArgumentException if {@code c} is {@code null}.
     * @throws NoDataException if {@code c} is empty.
     */
    public PolynomialFunction(double c[])
        throws NullArgumentException, NoDataException {
        super();
        MathUtils.checkNotNull(c);
        int n = c.length;
        if (n == 0) {
            throw new NoDataException(LocalizedFormats.EMPTY_POLYNOMIALS_COEFFICIENTS_ARRAY);
        }
        while ((n > 1) && (c[n - 1] == 0)) {
            --n;
        }
        this.coefficients = new double[n];
        System.arraycopy(c, 0, this.coefficients, 0, n);
    }

    /**
     * Compute the value of the function for the given argument.
     * <p>
     *  The value returned is </p><p>
     *  {@code coefficients[n] * x^n + ... + coefficients[1] * x  + coefficients[0]}
     * </p>
     *
     * @param x Argument for which the function value should be computed.
     * @return the value of the polynomial at the given point.
     * @see UnivariateFunction#value(double)
     */
    public double value(double x) {
       return evaluate(coefficients, x);
    }

    /**
     * Returns the degree of the polynomial.
     *
     * @return the degree of the polynomial.
     */
    public int degree() {
        return coefficients.length - 1;
    }

    /**
     * Returns a copy of the coefficients array.
     * <p>
     * Changes made to the returned copy will not affect the coefficients of
     * the polynomial.</p>
     *
     * @return a fresh copy of the coefficients array.
     */
    public double[] getCoefficients() {
        return coefficients.clone();
    }

    /**
     * Uses Horner's Method to evaluate the polynomial with the given coefficients at
     * the argument.
     *
     * @param coefficients Coefficients of the polynomial to evaluate.
     * @param argument Input value.
     * @return the value of the polynomial.
     * @throws NoDataException if {@code coefficients} is empty.
     * @throws NullArgumentException if {@code coefficients} is {@code null}.
     */
    protected static double evaluate(double[] coefficients, double argument)
        throws NullArgumentException, NoDataException {
        MathUtils.checkNotNull(coefficients);
        int n = coefficients.length;
        if (n == 0) {
            throw new NoDataException(LocalizedFormats.EMPTY_POLYNOMIALS_COEFFICIENTS_ARRAY);
        }
        double result = coefficients[n - 1];
        for (int j = n - 2; j >= 0; j--) {
            result = argument * result + coefficients[j];
        }
        return result;
    }


    /** {@inheritDoc}
     * @since 3.1
     * @throws NoDataException if {@code coefficients} is empty.
     * @throws NullArgumentException if {@code coefficients} is {@code null}.
     */
    public DerivativeStructure value(final DerivativeStructure t)
        throws NullArgumentException, NoDataException {
        MathUtils.checkNotNull(coefficients);
        int n = coefficients.length;
        if (n == 0) {
            throw new NoDataException(LocalizedFormats.EMPTY_POLYNOMIALS_COEFFICIENTS_ARRAY);
        }
        DerivativeStructure result =
                new DerivativeStructure(t.getFreeParameters(), t.getOrder(), coefficients[n - 1]);
        for (int j = n - 2; j >= 0; j--) {
            result = result.multiply(t).add(coefficients[j]);
        }
        return result;
    }

    /**
     * Add a polynomial to the instance.
     *
     * @param p Polynomial to add.
     * @return a new polynomial which is the sum of the instance and {@code p}.
     */
    public PolynomialFunction add(final PolynomialFunction p) {
        // identify the lowest degree polynomial
        final int lowLength  = FastMath.min(coefficients.length, p.coefficients.length);
        final int highLength = FastMath.max(coefficients.length, p.coefficients.length);

        // build the coefficients array
        double[] newCoefficients = new double[highLength];
        for (int i = 0; i < lowLength; ++i) {
            newCoefficients[i] = coefficients[i] + p.coefficients[i];
        }
        System.arraycopy((coefficients.length < p.coefficients.length) ?
                         p.coefficients : coefficients,
                         lowLength,
                         newCoefficients, lowLength,
                         highLength - lowLength);

        return new PolynomialFunction(newCoefficients);
    }

    /**
     * Subtract a polynomial from the instance.
     *
     * @param p Polynomial to subtract.
     * @return a new polynomial which is the instance minus {@code p}.
     */
    public PolynomialFunction subtract(final PolynomialFunction p) {
        // identify the lowest degree polynomial
        int lowLength  = FastMath.min(coefficients.length, p.coefficients.length);
        int highLength = FastMath.max(coefficients.length, p.coefficients.length);

        // build the coefficients array
        double[] newCoefficients = new double[highLength];
        for (int i = 0; i < lowLength; ++i) {
            newCoefficients[i] = coefficients[i] - p.coefficients[i];
        }
        if (coefficients.length < p.coefficients.length) {
            for (int i = lowLength; i < highLength; ++i) {
                newCoefficients[i] = -p.coefficients[i];
            }
        } else {
            System.arraycopy(coefficients, lowLength, newCoefficients, lowLength,
                             highLength - lowLength);
        }

        return new PolynomialFunction(newCoefficients);
    }

    /**
     * Negate the instance.
     *
     * @return a new polynomial with all coefficients negated
     */
    public PolynomialFunction negate() {
        double[] newCoefficients = new double[coefficients.length];
        for (int i = 0; i < coefficients.length; ++i) {
            newCoefficients[i] = -coefficients[i];
        }
        return new PolynomialFunction(newCoefficients);
    }

    /**
     * Multiply the instance by a polynomial.
     *
     * @param p Polynomial to multiply by.
     * @return a new polynomial equal to this times {@code p}
     */
    public PolynomialFunction multiply(final PolynomialFunction p) {
        double[] newCoefficients = new double[coefficients.length + p.coefficients.length - 1];

        for (int i = 0; i < newCoefficients.length; ++i) {
            newCoefficients[i] = 0.0;
            for (int j = FastMath.max(0, i + 1 - p.coefficients.length);
                 j < FastMath.min(coefficients.length, i + 1);
                 ++j) {
                newCoefficients[i] += coefficients[j] * p.coefficients[i-j];
            }
        }

        return new PolynomialFunction(newCoefficients);
    }

    /**
     * Returns the coefficients of the derivative of the polynomial with the given coefficients.
     *
     * @param coefficients Coefficients of the polynomial to differentiate.
     * @return the coefficients of the derivative or {@code null} if coefficients has length 1.
     * @throws NoDataException if {@code coefficients} is empty.
     * @throws NullArgumentException if {@code coefficients} is {@code null}.
     */
    protected static double[] differentiate(double[] coefficients)
        throws NullArgumentException, NoDataException {
        MathUtils.checkNotNull(coefficients);
        int n = coefficients.length;
        if (n == 0) {
            throw new NoDataException(LocalizedFormats.EMPTY_POLYNOMIALS_COEFFICIENTS_ARRAY);
        }
        if (n == 1) {
            return new double[]{0};
        }
        double[] result = new double[n - 1];
        for (int i = n - 1; i > 0; i--) {
            result[i - 1] = i * coefficients[i];
        }
        return result;
    }

    /**
     * Returns the derivative as a {@link PolynomialFunction}.
     *
     * @return the derivative polynomial.
     */
    public PolynomialFunction polynomialDerivative() {
        return new PolynomialFunction(differentiate(coefficients));
    }

    /**
     * Returns the derivative as a {@link UnivariateFunction}.
     *
     * @return the derivative function.
     */
    public UnivariateFunction derivative() {
        return polynomialDerivative();
    }

    /**
     * Returns a string representation of the polynomial.
     *
     * <p>The representation is user oriented. Terms are displayed lowest
     * degrees first. The multiplications signs, coefficients equals to
     * one and null terms are not displayed (except if the polynomial is 0,
     * in which case the 0 constant term is displayed). Addition of terms
     * with negative coefficients are replaced by subtraction of terms
     * with positive coefficients except for the first displayed term
     * (i.e. we display <code>-3</code> for a constant negative polynomial,
     * but <code>1 - 3 x + x^2</code> if the negative coefficient is not
     * the first one displayed).</p>
     *
     * @return a string representation of the polynomial.
     */
    @Override
    public String toString() {
        StringBuilder s = new StringBuilder();
        if (coefficients[0] == 0.0) {
            if (coefficients.length == 1) {
                return "0";
            }
        } else {
            s.append(toString(coefficients[0]));
        }

        for (int i = 1; i < coefficients.length; ++i) {
            if (coefficients[i] != 0) {
                if (s.length() > 0) {
                    if (coefficients[i] < 0) {
                        s.append(" - ");
                    } else {
                        s.append(" + ");
                    }
                } else {
                    if (coefficients[i] < 0) {
                        s.append("-");
                    }
                }

                double absAi = FastMath.abs(coefficients[i]);
                if ((absAi - 1) != 0) {
                    s.append(toString(absAi));
                    s.append(' ');
                }

                s.append("x");
                if (i > 1) {
                    s.append('^');
                    s.append(Integer.toString(i));
                }
            }
        }

        return s.toString();
    }

    /**
     * Creates a string representing a coefficient, removing ".0" endings.
     *
     * @param coeff Coefficient.
     * @return a string representation of {@code coeff}.
     */
    private static String toString(double coeff) {
        final String c = Double.toString(coeff);
        if (c.endsWith(".0")) {
            return c.substring(0, c.length() - 2);
        } else {
            return c;
        }
    }

    /** {@inheritDoc} */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + Arrays.hashCode(coefficients);
        return result;
    }

    /** {@inheritDoc} */
    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (!(obj instanceof PolynomialFunction)) {
            return false;
        }
        PolynomialFunction other = (PolynomialFunction) obj;
        if (!Arrays.equals(coefficients, other.coefficients)) {
            return false;
        }
        return true;
    }

    /**
     * Dedicated parametric polynomial class.
     *
     * @since 3.0
     */
    public static class Parametric implements ParametricUnivariateFunction {
        /** {@inheritDoc} */
        public double[] gradient(double x, double ... parameters) {
            final double[] gradient = new double[parameters.length];
            double xn = 1.0;
            for (int i = 0; i < parameters.length; ++i) {
                gradient[i] = xn;
                xn *= x;
            }
            return gradient;
        }

        /** {@inheritDoc} */
        public double value(final double x, final double ... parameters)
            throws NoDataException {
            return PolynomialFunction.evaluate(parameters, x);
        }
    }
}
