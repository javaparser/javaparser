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
package org.apache.commons.math3;

import org.apache.commons.math3.exception.DimensionMismatchException;

/**
 * Interface representing a <a href="http://mathworld.wolfram.com/RealNumber.html">real</a>
 * <a href="http://mathworld.wolfram.com/Field.html">field</a>.
 * @param <T> the type of the field elements
 * @see FieldElement
 * @since 3.2
 */
public interface RealFieldElement<T> extends FieldElement<T> {

    /** Get the real value of the number.
     * @return real value
     */
    double getReal();

    /** '+' operator.
     * @param a right hand side parameter of the operator
     * @return this+a
     */
    T add(double a);

    /** '-' operator.
     * @param a right hand side parameter of the operator
     * @return this-a
     */
    T subtract(double a);

    /** '&times;' operator.
     * @param a right hand side parameter of the operator
     * @return this&times;a
     */
    T multiply(double a);

    /** '&divide;' operator.
     * @param a right hand side parameter of the operator
     * @return this&divide;a
     */
    T divide(double a);

    /** IEEE remainder operator.
     * @param a right hand side parameter of the operator
     * @return this - n &times; a where n is the closest integer to this/a
     * (the even integer is chosen for n if this/a is halfway between two integers)
     */
    T remainder(double a);

    /** IEEE remainder operator.
     * @param a right hand side parameter of the operator
     * @return this - n &times; a where n is the closest integer to this/a
     * (the even integer is chosen for n if this/a is halfway between two integers)
     * @exception DimensionMismatchException if number of free parameters or orders are inconsistent
     */
    T remainder(T a)
        throws DimensionMismatchException;

    /** absolute value.
     * @return abs(this)
     */
    T abs();

    /** Get the smallest whole number larger than instance.
     * @return ceil(this)
     */
    T ceil();

    /** Get the largest whole number smaller than instance.
     * @return floor(this)
     */
    T floor();

    /** Get the whole number that is the nearest to the instance, or the even one if x is exactly half way between two integers.
     * @return a double number r such that r is an integer r - 0.5 &le; this &le; r + 0.5
     */
    T rint();

    /** Get the closest long to instance value.
     * @return closest long to {@link #getReal()}
     */
    long round();

    /** Compute the signum of the instance.
     * The signum is -1 for negative numbers, +1 for positive numbers and 0 otherwise
     * @return -1.0, -0.0, +0.0, +1.0 or NaN depending on sign of a
     */
    T signum();

    /**
     * Returns the instance with the sign of the argument.
     * A NaN {@code sign} argument is treated as positive.
     *
     * @param sign the sign for the returned value
     * @return the instance with the same sign as the {@code sign} argument
     */
    T copySign(T sign);

    /**
     * Returns the instance with the sign of the argument.
     * A NaN {@code sign} argument is treated as positive.
     *
     * @param sign the sign for the returned value
     * @return the instance with the same sign as the {@code sign} argument
     */
    T copySign(double sign);

    /**
     * Multiply the instance by a power of 2.
     * @param n power of 2
     * @return this &times; 2<sup>n</sup>
     */
    T scalb(int n);

    /**
     * Returns the hypotenuse of a triangle with sides {@code this} and {@code y}
     * - sqrt(<i>this</i><sup>2</sup>&nbsp;+<i>y</i><sup>2</sup>)
     * avoiding intermediate overflow or underflow.
     *
     * <ul>
     * <li> If either argument is infinite, then the result is positive infinity.</li>
     * <li> else, if either argument is NaN then the result is NaN.</li>
     * </ul>
     *
     * @param y a value
     * @return sqrt(<i>this</i><sup>2</sup>&nbsp;+<i>y</i><sup>2</sup>)
     * @exception DimensionMismatchException if number of free parameters or orders are inconsistent
     */
    T hypot(T y)
        throws DimensionMismatchException;

    /** {@inheritDoc} */
    T reciprocal();

    /** Square root.
     * @return square root of the instance
     */
    T sqrt();

    /** Cubic root.
     * @return cubic root of the instance
     */
    T cbrt();

    /** N<sup>th</sup> root.
     * @param n order of the root
     * @return n<sup>th</sup> root of the instance
     */
    T rootN(int n);

    /** Power operation.
     * @param p power to apply
     * @return this<sup>p</sup>
     */
    T pow(double p);

    /** Integer power operation.
     * @param n power to apply
     * @return this<sup>n</sup>
     */
    T pow(int n);

    /** Power operation.
     * @param e exponent
     * @return this<sup>e</sup>
     * @exception DimensionMismatchException if number of free parameters or orders are inconsistent
     */
    T pow(T e)
        throws DimensionMismatchException;

    /** Exponential.
     * @return exponential of the instance
     */
    T exp();

    /** Exponential minus 1.
     * @return exponential minus one of the instance
     */
    T expm1();

    /** Natural logarithm.
     * @return logarithm of the instance
     */
    T log();

    /** Shifted natural logarithm.
     * @return logarithm of one plus the instance
     */
    T log1p();

//    TODO: add this method in 4.0, as it is not possible to do it in 3.2
//          due to incompatibility of the return type in the Dfp class
//    /** Base 10 logarithm.
//     * @return base 10 logarithm of the instance
//     */
//    T log10();

    /** Cosine operation.
     * @return cos(this)
     */
    T cos();

    /** Sine operation.
     * @return sin(this)
     */
    T sin();

    /** Tangent operation.
     * @return tan(this)
     */
    T tan();

    /** Arc cosine operation.
     * @return acos(this)
     */
    T acos();

    /** Arc sine operation.
     * @return asin(this)
     */
    T asin();

    /** Arc tangent operation.
     * @return atan(this)
     */
    T atan();

    /** Two arguments arc tangent operation.
     * @param x second argument of the arc tangent
     * @return atan2(this, x)
     * @exception DimensionMismatchException if number of free parameters or orders are inconsistent
     */
    T atan2(T x)
        throws DimensionMismatchException;

    /** Hyperbolic cosine operation.
     * @return cosh(this)
     */
    T cosh();

    /** Hyperbolic sine operation.
     * @return sinh(this)
     */
    T sinh();

    /** Hyperbolic tangent operation.
     * @return tanh(this)
     */
    T tanh();

    /** Inverse hyperbolic cosine operation.
     * @return acosh(this)
     */
    T acosh();

    /** Inverse hyperbolic sine operation.
     * @return asin(this)
     */
    T asinh();

    /** Inverse hyperbolic  tangent operation.
     * @return atanh(this)
     */
    T atanh();

    /**
     * Compute a linear combination.
     * @param a Factors.
     * @param b Factors.
     * @return <code>&Sigma;<sub>i</sub> a<sub>i</sub> b<sub>i</sub></code>.
     * @throws DimensionMismatchException if arrays dimensions don't match
     * @since 3.2
     */
    T linearCombination(T[] a, T[] b)
        throws DimensionMismatchException;

    /**
     * Compute a linear combination.
     * @param a Factors.
     * @param b Factors.
     * @return <code>&Sigma;<sub>i</sub> a<sub>i</sub> b<sub>i</sub></code>.
     * @throws DimensionMismatchException if arrays dimensions don't match
     * @since 3.2
     */
    T linearCombination(double[] a, T[] b)
        throws DimensionMismatchException;

    /**
     * Compute a linear combination.
     * @param a1 first factor of the first term
     * @param b1 second factor of the first term
     * @param a2 first factor of the second term
     * @param b2 second factor of the second term
     * @return a<sub>1</sub>&times;b<sub>1</sub> +
     * a<sub>2</sub>&times;b<sub>2</sub>
     * @see #linearCombination(Object, Object, Object, Object, Object, Object)
     * @see #linearCombination(Object, Object, Object, Object, Object, Object, Object, Object)
     * @since 3.2
     */
    T linearCombination(T a1, T b1, T a2, T b2);

    /**
     * Compute a linear combination.
     * @param a1 first factor of the first term
     * @param b1 second factor of the first term
     * @param a2 first factor of the second term
     * @param b2 second factor of the second term
     * @return a<sub>1</sub>&times;b<sub>1</sub> +
     * a<sub>2</sub>&times;b<sub>2</sub>
     * @see #linearCombination(double, Object, double, Object, double, Object)
     * @see #linearCombination(double, Object, double, Object, double, Object, double, Object)
     * @since 3.2
     */
    T linearCombination(double a1, T b1, double a2, T b2);

    /**
     * Compute a linear combination.
     * @param a1 first factor of the first term
     * @param b1 second factor of the first term
     * @param a2 first factor of the second term
     * @param b2 second factor of the second term
     * @param a3 first factor of the third term
     * @param b3 second factor of the third term
     * @return a<sub>1</sub>&times;b<sub>1</sub> +
     * a<sub>2</sub>&times;b<sub>2</sub> + a<sub>3</sub>&times;b<sub>3</sub>
     * @see #linearCombination(Object, Object, Object, Object)
     * @see #linearCombination(Object, Object, Object, Object, Object, Object, Object, Object)
     * @since 3.2
     */
    T linearCombination(T a1, T b1, T a2, T b2, T a3, T b3);

    /**
     * Compute a linear combination.
     * @param a1 first factor of the first term
     * @param b1 second factor of the first term
     * @param a2 first factor of the second term
     * @param b2 second factor of the second term
     * @param a3 first factor of the third term
     * @param b3 second factor of the third term
     * @return a<sub>1</sub>&times;b<sub>1</sub> +
     * a<sub>2</sub>&times;b<sub>2</sub> + a<sub>3</sub>&times;b<sub>3</sub>
     * @see #linearCombination(double, Object, double, Object)
     * @see #linearCombination(double, Object, double, Object, double, Object, double, Object)
     * @since 3.2
     */
    T linearCombination(double a1, T b1,  double a2, T b2, double a3, T b3);

    /**
     * Compute a linear combination.
     * @param a1 first factor of the first term
     * @param b1 second factor of the first term
     * @param a2 first factor of the second term
     * @param b2 second factor of the second term
     * @param a3 first factor of the third term
     * @param b3 second factor of the third term
     * @param a4 first factor of the third term
     * @param b4 second factor of the third term
     * @return a<sub>1</sub>&times;b<sub>1</sub> +
     * a<sub>2</sub>&times;b<sub>2</sub> + a<sub>3</sub>&times;b<sub>3</sub> +
     * a<sub>4</sub>&times;b<sub>4</sub>
     * @see #linearCombination(Object, Object, Object, Object)
     * @see #linearCombination(Object, Object, Object, Object, Object, Object)
     * @since 3.2
     */
    T linearCombination(T a1, T b1, T a2, T b2, T a3, T b3, T a4, T b4);

    /**
     * Compute a linear combination.
     * @param a1 first factor of the first term
     * @param b1 second factor of the first term
     * @param a2 first factor of the second term
     * @param b2 second factor of the second term
     * @param a3 first factor of the third term
     * @param b3 second factor of the third term
     * @param a4 first factor of the third term
     * @param b4 second factor of the third term
     * @return a<sub>1</sub>&times;b<sub>1</sub> +
     * a<sub>2</sub>&times;b<sub>2</sub> + a<sub>3</sub>&times;b<sub>3</sub> +
     * a<sub>4</sub>&times;b<sub>4</sub>
     * @see #linearCombination(double, Object, double, Object)
     * @see #linearCombination(double, Object, double, Object, double, Object)
     * @since 3.2
     */
    T linearCombination(double a1, T b1, double a2, T b2, double a3, T b3, double a4, T b4);

}
