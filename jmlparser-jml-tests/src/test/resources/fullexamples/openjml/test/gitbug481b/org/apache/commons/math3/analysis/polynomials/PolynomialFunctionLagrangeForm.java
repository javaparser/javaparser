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

import org.apache.commons.math3.analysis.UnivariateFunction;
import org.apache.commons.math3.util.FastMath;
import org.apache.commons.math3.util.MathArrays;
import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.NonMonotonicSequenceException;
import org.apache.commons.math3.exception.NumberIsTooSmallException;
import org.apache.commons.math3.exception.util.LocalizedFormats;

/**
 * Implements the representation of a real polynomial function in
 * <a href="http://mathworld.wolfram.com/LagrangeInterpolatingPolynomial.html">
 * Lagrange Form</a>. For reference, see <b>Introduction to Numerical
 * Analysis</b>, ISBN 038795452X, chapter 2.
 * <p>
 * The approximated function should be smooth enough for Lagrange polynomial
 * to work well. Otherwise, consider using splines instead.</p>
 *
 * @since 1.2
 */
public class PolynomialFunctionLagrangeForm implements UnivariateFunction {
    /**
     * The coefficients of the polynomial, ordered by degree -- i.e.
     * coefficients[0] is the constant term and coefficients[n] is the
     * coefficient of x^n where n is the degree of the polynomial.
     */
    private double coefficients[];
    /**
     * Interpolating points (abscissas).
     */
    private final double x[];
    /**
     * Function values at interpolating points.
     */
    private final double y[];
    /**
     * Whether the polynomial coefficients are available.
     */
    private boolean coefficientsComputed;

    /**
     * Construct a Lagrange polynomial with the given abscissas and function
     * values. The order of interpolating points are not important.
     * <p>
     * The constructor makes copy of the input arrays and assigns them.</p>
     *
     * @param x interpolating points
     * @param y function values at interpolating points
     * @throws DimensionMismatchException if the array lengths are different.
     * @throws NumberIsTooSmallException if the number of points is less than 2.
     * @throws NonMonotonicSequenceException
     * if two abscissae have the same value.
     */
    public PolynomialFunctionLagrangeForm(double x[], double y[])
        throws DimensionMismatchException, NumberIsTooSmallException, NonMonotonicSequenceException {
        this.x = new double[x.length];
        this.y = new double[y.length];
        System.arraycopy(x, 0, this.x, 0, x.length);
        System.arraycopy(y, 0, this.y, 0, y.length);
        coefficientsComputed = false;

        if (!verifyInterpolationArray(x, y, false)) {
            MathArrays.sortInPlace(this.x, this.y);
            // Second check in case some abscissa is duplicated.
            verifyInterpolationArray(this.x, this.y, true);
        }
    }

    /**
     * Calculate the function value at the given point.
     *
     * @param z Point at which the function value is to be computed.
     * @return the function value.
     * @throws DimensionMismatchException if {@code x} and {@code y} have
     * different lengths.
     * @throws org.apache.commons.math3.exception.NonMonotonicSequenceException
     * if {@code x} is not sorted in strictly increasing order.
     * @throws NumberIsTooSmallException if the size of {@code x} is less
     * than 2.
     */
    public double value(double z) {
        return evaluateInternal(x, y, z);
    }

    /**
     * Returns the degree of the polynomial.
     *
     * @return the degree of the polynomial
     */
    public int degree() {
        return x.length - 1;
    }

    /**
     * Returns a copy of the interpolating points array.
     * <p>
     * Changes made to the returned copy will not affect the polynomial.</p>
     *
     * @return a fresh copy of the interpolating points array
     */
    public double[] getInterpolatingPoints() {
        double[] out = new double[x.length];
        System.arraycopy(x, 0, out, 0, x.length);
        return out;
    }

    /**
     * Returns a copy of the interpolating values array.
     * <p>
     * Changes made to the returned copy will not affect the polynomial.</p>
     *
     * @return a fresh copy of the interpolating values array
     */
    public double[] getInterpolatingValues() {
        double[] out = new double[y.length];
        System.arraycopy(y, 0, out, 0, y.length);
        return out;
    }

    /**
     * Returns a copy of the coefficients array.
     * <p>
     * Changes made to the returned copy will not affect the polynomial.</p>
     * <p>
     * Note that coefficients computation can be ill-conditioned. Use with caution
     * and only when it is necessary.</p>
     *
     * @return a fresh copy of the coefficients array
     */
    public double[] getCoefficients() {
        if (!coefficientsComputed) {
            computeCoefficients();
        }
        double[] out = new double[coefficients.length];
        System.arraycopy(coefficients, 0, out, 0, coefficients.length);
        return out;
    }

    /**
     * Evaluate the Lagrange polynomial using
     * <a href="http://mathworld.wolfram.com/NevillesAlgorithm.html">
     * Neville's Algorithm</a>. It takes O(n^2) time.
     *
     * @param x Interpolating points array.
     * @param y Interpolating values array.
     * @param z Point at which the function value is to be computed.
     * @return the function value.
     * @throws DimensionMismatchException if {@code x} and {@code y} have
     * different lengths.
     * @throws NonMonotonicSequenceException
     * if {@code x} is not sorted in strictly increasing order.
     * @throws NumberIsTooSmallException if the size of {@code x} is less
     * than 2.
     */
    public static double evaluate(double x[], double y[], double z)
        throws DimensionMismatchException, NumberIsTooSmallException, NonMonotonicSequenceException {
        if (verifyInterpolationArray(x, y, false)) {
            return evaluateInternal(x, y, z);
        }

        // Array is not sorted.
        final double[] xNew = new double[x.length];
        final double[] yNew = new double[y.length];
        System.arraycopy(x, 0, xNew, 0, x.length);
        System.arraycopy(y, 0, yNew, 0, y.length);

        MathArrays.sortInPlace(xNew, yNew);
        // Second check in case some abscissa is duplicated.
        verifyInterpolationArray(xNew, yNew, true);
        return evaluateInternal(xNew, yNew, z);
    }

    /**
     * Evaluate the Lagrange polynomial using
     * <a href="http://mathworld.wolfram.com/NevillesAlgorithm.html">
     * Neville's Algorithm</a>. It takes O(n^2) time.
     *
     * @param x Interpolating points array.
     * @param y Interpolating values array.
     * @param z Point at which the function value is to be computed.
     * @return the function value.
     * @throws DimensionMismatchException if {@code x} and {@code y} have
     * different lengths.
     * @throws org.apache.commons.math3.exception.NonMonotonicSequenceException
     * if {@code x} is not sorted in strictly increasing order.
     * @throws NumberIsTooSmallException if the size of {@code x} is less
     * than 2.
     */
    private static double evaluateInternal(double x[], double y[], double z) {
        int nearest = 0;
        final int n = x.length;
        final double[] c = new double[n];
        final double[] d = new double[n];
        double min_dist = Double.POSITIVE_INFINITY;
        for (int i = 0; i < n; i++) {
            // initialize the difference arrays
            c[i] = y[i];
            d[i] = y[i];
            // find out the abscissa closest to z
            final double dist = FastMath.abs(z - x[i]);
            if (dist < min_dist) {
                nearest = i;
                min_dist = dist;
            }
        }

        // initial approximation to the function value at z
        double value = y[nearest];

        for (int i = 1; i < n; i++) {
            for (int j = 0; j < n-i; j++) {
                final double tc = x[j] - z;
                final double td = x[i+j] - z;
                final double divider = x[j] - x[i+j];
                // update the difference arrays
                final double w = (c[j+1] - d[j]) / divider;
                c[j] = tc * w;
                d[j] = td * w;
            }
            // sum up the difference terms to get the final value
            if (nearest < 0.5*(n-i+1)) {
                value += c[nearest];    // fork down
            } else {
                nearest--;
                value += d[nearest];    // fork up
            }
        }

        return value;
    }

    /**
     * Calculate the coefficients of Lagrange polynomial from the
     * interpolation data. It takes O(n^2) time.
     * Note that this computation can be ill-conditioned: Use with caution
     * and only when it is necessary.
     */
    protected void computeCoefficients() {
        final int n = degree() + 1;
        coefficients = new double[n];
        for (int i = 0; i < n; i++) {
            coefficients[i] = 0.0;
        }

        // c[] are the coefficients of P(x) = (x-x[0])(x-x[1])...(x-x[n-1])
        final double[] c = new double[n+1];
        c[0] = 1.0;
        for (int i = 0; i < n; i++) {
            for (int j = i; j > 0; j--) {
                c[j] = c[j-1] - c[j] * x[i];
            }
            c[0] *= -x[i];
            c[i+1] = 1;
        }

        final double[] tc = new double[n];
        for (int i = 0; i < n; i++) {
            // d = (x[i]-x[0])...(x[i]-x[i-1])(x[i]-x[i+1])...(x[i]-x[n-1])
            double d = 1;
            for (int j = 0; j < n; j++) {
                if (i != j) {
                    d *= x[i] - x[j];
                }
            }
            final double t = y[i] / d;
            // Lagrange polynomial is the sum of n terms, each of which is a
            // polynomial of degree n-1. tc[] are the coefficients of the i-th
            // numerator Pi(x) = (x-x[0])...(x-x[i-1])(x-x[i+1])...(x-x[n-1]).
            tc[n-1] = c[n];     // actually c[n] = 1
            coefficients[n-1] += t * tc[n-1];
            for (int j = n-2; j >= 0; j--) {
                tc[j] = c[j+1] + tc[j+1] * x[i];
                coefficients[j] += t * tc[j];
            }
        }

        coefficientsComputed = true;
    }

    /**
     * Check that the interpolation arrays are valid.
     * The arrays features checked by this method are that both arrays have the
     * same length and this length is at least 2.
     *
     * @param x Interpolating points array.
     * @param y Interpolating values array.
     * @param abort Whether to throw an exception if {@code x} is not sorted.
     * @throws DimensionMismatchException if the array lengths are different.
     * @throws NumberIsTooSmallException if the number of points is less than 2.
     * @throws org.apache.commons.math3.exception.NonMonotonicSequenceException
     * if {@code x} is not sorted in strictly increasing order and {@code abort}
     * is {@code true}.
     * @return {@code false} if the {@code x} is not sorted in increasing order,
     * {@code true} otherwise.
     * @see #evaluate(double[], double[], double)
     * @see #computeCoefficients()
     */
    public static boolean verifyInterpolationArray(double x[], double y[], boolean abort)
        throws DimensionMismatchException, NumberIsTooSmallException, NonMonotonicSequenceException {
        if (x.length != y.length) {
            throw new DimensionMismatchException(x.length, y.length);
        }
        if (x.length < 2) {
            throw new NumberIsTooSmallException(LocalizedFormats.WRONG_NUMBER_OF_POINTS, 2, x.length, true);
        }

        return MathArrays.checkOrder(x, MathArrays.OrderDirection.INCREASING, true, abort);
    }
}
