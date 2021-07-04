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
package org.apache.commons.math3.analysis.differentiation;

import java.io.Serializable;

import org.apache.commons.math3.Field;
import org.apache.commons.math3.FieldElement;
import org.apache.commons.math3.RealFieldElement;
import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.MathArithmeticException;
import org.apache.commons.math3.exception.NumberIsTooLargeException;
import org.apache.commons.math3.util.FastMath;
import org.apache.commons.math3.util.MathArrays;
import org.apache.commons.math3.util.MathUtils;

/** Class representing both the value and the differentials of a function.
 * <p>This class is the workhorse of the differentiation package.</p>
 * <p>This class is an implementation of the extension to Rall's
 * numbers described in Dan Kalman's paper <a
 * href="http://www1.american.edu/cas/mathstat/People/kalman/pdffiles/mmgautodiff.pdf">Doubly
 * Recursive Multivariate Automatic Differentiation</a>, Mathematics Magazine, vol. 75,
 * no. 3, June 2002. Rall's numbers are an extension to the real numbers used
 * throughout mathematical expressions; they hold the derivative together with the
 * value of a function. Dan Kalman's derivative structures hold all partial derivatives
 * up to any specified order, with respect to any number of free parameters. Rall's
 * numbers therefore can be seen as derivative structures for order one derivative and
 * one free parameter, and real numbers can be seen as derivative structures with zero
 * order derivative and no free parameters.</p>
 * <p>{@link DerivativeStructure} instances can be used directly thanks to
 * the arithmetic operators to the mathematical functions provided as
 * methods by this class (+, -, *, /, %, sin, cos ...).</p>
 * <p>Implementing complex expressions by hand using these classes is
 * a tedious and error-prone task but has the advantage of having no limitation
 * on the derivation order despite no requiring users to compute the derivatives by
 * themselves. Implementing complex expression can also be done by developing computation
 * code using standard primitive double values and to use {@link
 * UnivariateFunctionDifferentiator differentiators} to create the {@link
 * DerivativeStructure}-based instances. This method is simpler but may be limited in
 * the accuracy and derivation orders and may be computationally intensive (this is
 * typically the case for {@link FiniteDifferencesDifferentiator finite differences
 * differentiator}.</p>
 * <p>Instances of this class are guaranteed to be immutable.</p>
 * @see DSCompiler
 * @since 3.1
 */
public class DerivativeStructure implements RealFieldElement<DerivativeStructure>, Serializable {

    /** Serializable UID. */
    private static final long serialVersionUID = 20120730L;

    /** Compiler for the current dimensions. */
    private transient DSCompiler compiler;

    /** Combined array holding all values. */
    private final double[] data;

    /** Build an instance with all values and derivatives set to 0.
     * @param compiler compiler to use for computation
     */
    private DerivativeStructure(final DSCompiler compiler) {
        this.compiler = compiler;
        this.data     = new double[compiler.getSize()];
    }

    /** Build an instance with all values and derivatives set to 0.
     * @param parameters number of free parameters
     * @param order derivation order
     * @throws NumberIsTooLargeException if order is too large
     */
    public DerivativeStructure(final int parameters, final int order)
        throws NumberIsTooLargeException {
        this(DSCompiler.getCompiler(parameters, order));
    }

    /** Build an instance representing a constant value.
     * @param parameters number of free parameters
     * @param order derivation order
     * @param value value of the constant
     * @throws NumberIsTooLargeException if order is too large
     * @see #DerivativeStructure(int, int, int, double)
     */
    public DerivativeStructure(final int parameters, final int order, final double value)
        throws NumberIsTooLargeException {
        this(parameters, order);
        this.data[0] = value;
    }

    /** Build an instance representing a variable.
     * <p>Instances built using this constructor are considered
     * to be the free variables with respect to which differentials
     * are computed. As such, their differential with respect to
     * themselves is +1.</p>
     * @param parameters number of free parameters
     * @param order derivation order
     * @param index index of the variable (from 0 to {@code parameters - 1})
     * @param value value of the variable
     * @exception NumberIsTooLargeException if {@code index >= parameters}.
     * @see #DerivativeStructure(int, int, double)
     */
    public DerivativeStructure(final int parameters, final int order,
                               final int index, final double value)
        throws NumberIsTooLargeException {
        this(parameters, order, value);

        if (index >= parameters) {
            throw new NumberIsTooLargeException(index, parameters, false);
        }

        if (order > 0) {
            // the derivative of the variable with respect to itself is 1.
            data[DSCompiler.getCompiler(index, order).getSize()] = 1.0;
        }

    }

    /** Linear combination constructor.
     * The derivative structure built will be a1 * ds1 + a2 * ds2
     * @param a1 first scale factor
     * @param ds1 first base (unscaled) derivative structure
     * @param a2 second scale factor
     * @param ds2 second base (unscaled) derivative structure
     * @exception DimensionMismatchException if number of free parameters or orders are inconsistent
     */
    public DerivativeStructure(final double a1, final DerivativeStructure ds1,
                               final double a2, final DerivativeStructure ds2)
        throws DimensionMismatchException {
        this(ds1.compiler);
        compiler.checkCompatibility(ds2.compiler);
        compiler.linearCombination(a1, ds1.data, 0, a2, ds2.data, 0, data, 0);
    }

    /** Linear combination constructor.
     * The derivative structure built will be a1 * ds1 + a2 * ds2 + a3 * ds3
     * @param a1 first scale factor
     * @param ds1 first base (unscaled) derivative structure
     * @param a2 second scale factor
     * @param ds2 second base (unscaled) derivative structure
     * @param a3 third scale factor
     * @param ds3 third base (unscaled) derivative structure
     * @exception DimensionMismatchException if number of free parameters or orders are inconsistent
     */
    public DerivativeStructure(final double a1, final DerivativeStructure ds1,
                               final double a2, final DerivativeStructure ds2,
                               final double a3, final DerivativeStructure ds3)
        throws DimensionMismatchException {
        this(ds1.compiler);
        compiler.checkCompatibility(ds2.compiler);
        compiler.checkCompatibility(ds3.compiler);
        compiler.linearCombination(a1, ds1.data, 0, a2, ds2.data, 0, a3, ds3.data, 0, data, 0);
    }

    /** Linear combination constructor.
     * The derivative structure built will be a1 * ds1 + a2 * ds2 + a3 * ds3 + a4 * ds4
     * @param a1 first scale factor
     * @param ds1 first base (unscaled) derivative structure
     * @param a2 second scale factor
     * @param ds2 second base (unscaled) derivative structure
     * @param a3 third scale factor
     * @param ds3 third base (unscaled) derivative structure
     * @param a4 fourth scale factor
     * @param ds4 fourth base (unscaled) derivative structure
     * @exception DimensionMismatchException if number of free parameters or orders are inconsistent
     */
    public DerivativeStructure(final double a1, final DerivativeStructure ds1,
                               final double a2, final DerivativeStructure ds2,
                               final double a3, final DerivativeStructure ds3,
                               final double a4, final DerivativeStructure ds4)
        throws DimensionMismatchException {
        this(ds1.compiler);
        compiler.checkCompatibility(ds2.compiler);
        compiler.checkCompatibility(ds3.compiler);
        compiler.checkCompatibility(ds4.compiler);
        compiler.linearCombination(a1, ds1.data, 0, a2, ds2.data, 0,
                                   a3, ds3.data, 0, a4, ds4.data, 0,
                                   data, 0);
    }

    /** Build an instance from all its derivatives.
     * @param parameters number of free parameters
     * @param order derivation order
     * @param derivatives derivatives sorted according to
     * {@link DSCompiler#getPartialDerivativeIndex(int...)}
     * @exception DimensionMismatchException if derivatives array does not match the
     * {@link DSCompiler#getSize() size} expected by the compiler
     * @throws NumberIsTooLargeException if order is too large
     * @see #getAllDerivatives()
     */
    public DerivativeStructure(final int parameters, final int order, final double ... derivatives)
        throws DimensionMismatchException, NumberIsTooLargeException {
        this(parameters, order);
        if (derivatives.length != data.length) {
            throw new DimensionMismatchException(derivatives.length, data.length);
        }
        System.arraycopy(derivatives, 0, data, 0, data.length);
    }

    /** Copy constructor.
     * @param ds instance to copy
     */
    private DerivativeStructure(final DerivativeStructure ds) {
        this.compiler = ds.compiler;
        this.data     = ds.data.clone();
    }

    /** Get the number of free parameters.
     * @return number of free parameters
     */
    public int getFreeParameters() {
        return compiler.getFreeParameters();
    }

    /** Get the derivation order.
     * @return derivation order
     */
    public int getOrder() {
        return compiler.getOrder();
    }

    /** Create a constant compatible with instance order and number of parameters.
     * <p>
     * This method is a convenience factory method, it simply calls
     * {@code new DerivativeStructure(getFreeParameters(), getOrder(), c)}
     * </p>
     * @param c value of the constant
     * @return a constant compatible with instance order and number of parameters
     * @see #DerivativeStructure(int, int, double)
     * @since 3.3
     */
    public DerivativeStructure createConstant(final double c) {
        return new DerivativeStructure(getFreeParameters(), getOrder(), c);
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public double getReal() {
        return data[0];
    }

    /** Get the value part of the derivative structure.
     * @return value part of the derivative structure
     * @see #getPartialDerivative(int...)
     */
    public double getValue() {
        return data[0];
    }

    /** Get a partial derivative.
     * @param orders derivation orders with respect to each variable (if all orders are 0,
     * the value is returned)
     * @return partial derivative
     * @see #getValue()
     * @exception DimensionMismatchException if the numbers of variables does not
     * match the instance
     * @exception NumberIsTooLargeException if sum of derivation orders is larger
     * than the instance limits
     */
    public double getPartialDerivative(final int ... orders)
        throws DimensionMismatchException, NumberIsTooLargeException {
        return data[compiler.getPartialDerivativeIndex(orders)];
    }

    /** Get all partial derivatives.
     * @return a fresh copy of partial derivatives, in an array sorted according to
     * {@link DSCompiler#getPartialDerivativeIndex(int...)}
     */
    public double[] getAllDerivatives() {
        return data.clone();
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public DerivativeStructure add(final double a) {
        final DerivativeStructure ds = new DerivativeStructure(this);
        ds.data[0] += a;
        return ds;
    }

    /** {@inheritDoc}
     * @exception DimensionMismatchException if number of free parameters
     * or orders do not match
     */
    public DerivativeStructure add(final DerivativeStructure a)
        throws DimensionMismatchException {
        compiler.checkCompatibility(a.compiler);
        final DerivativeStructure ds = new DerivativeStructure(this);
        compiler.add(data, 0, a.data, 0, ds.data, 0);
        return ds;
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public DerivativeStructure subtract(final double a) {
        return add(-a);
    }

    /** {@inheritDoc}
     * @exception DimensionMismatchException if number of free parameters
     * or orders do not match
     */
    public DerivativeStructure subtract(final DerivativeStructure a)
        throws DimensionMismatchException {
        compiler.checkCompatibility(a.compiler);
        final DerivativeStructure ds = new DerivativeStructure(this);
        compiler.subtract(data, 0, a.data, 0, ds.data, 0);
        return ds;
    }

    /** {@inheritDoc} */
    public DerivativeStructure multiply(final int n) {
        return multiply((double) n);
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public DerivativeStructure multiply(final double a) {
        final DerivativeStructure ds = new DerivativeStructure(this);
        for (int i = 0; i < ds.data.length; ++i) {
            ds.data[i] *= a;
        }
        return ds;
    }

    /** {@inheritDoc}
     * @exception DimensionMismatchException if number of free parameters
     * or orders do not match
     */
    public DerivativeStructure multiply(final DerivativeStructure a)
        throws DimensionMismatchException {
        compiler.checkCompatibility(a.compiler);
        final DerivativeStructure result = new DerivativeStructure(compiler);
        compiler.multiply(data, 0, a.data, 0, result.data, 0);
        return result;
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public DerivativeStructure divide(final double a) {
        final DerivativeStructure ds = new DerivativeStructure(this);
        for (int i = 0; i < ds.data.length; ++i) {
            ds.data[i] /= a;
        }
        return ds;
    }

    /** {@inheritDoc}
     * @exception DimensionMismatchException if number of free parameters
     * or orders do not match
     */
    public DerivativeStructure divide(final DerivativeStructure a)
        throws DimensionMismatchException {
        compiler.checkCompatibility(a.compiler);
        final DerivativeStructure result = new DerivativeStructure(compiler);
        compiler.divide(data, 0, a.data, 0, result.data, 0);
        return result;
    }

    /** {@inheritDoc} */
    public DerivativeStructure remainder(final double a) {
        final DerivativeStructure ds = new DerivativeStructure(this);
        ds.data[0] = FastMath.IEEEremainder(ds.data[0], a);
        return ds;
    }

    /** {@inheritDoc}
     * @exception DimensionMismatchException if number of free parameters
     * or orders do not match
     * @since 3.2
     */
    public DerivativeStructure remainder(final DerivativeStructure a)
        throws DimensionMismatchException {
        compiler.checkCompatibility(a.compiler);
        final DerivativeStructure result = new DerivativeStructure(compiler);
        compiler.remainder(data, 0, a.data, 0, result.data, 0);
        return result;
    }

    /** {@inheritDoc} */
    public DerivativeStructure negate() {
        final DerivativeStructure ds = new DerivativeStructure(compiler);
        for (int i = 0; i < ds.data.length; ++i) {
            ds.data[i] = -data[i];
        }
        return ds;
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public DerivativeStructure abs() {
        if (Double.doubleToLongBits(data[0]) < 0) {
            // we use the bits representation to also handle -0.0
            return negate();
        } else {
            return this;
        }
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public DerivativeStructure ceil() {
        return new DerivativeStructure(compiler.getFreeParameters(),
                                       compiler.getOrder(),
                                       FastMath.ceil(data[0]));
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public DerivativeStructure floor() {
        return new DerivativeStructure(compiler.getFreeParameters(),
                                       compiler.getOrder(),
                                       FastMath.floor(data[0]));
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public DerivativeStructure rint() {
        return new DerivativeStructure(compiler.getFreeParameters(),
                                       compiler.getOrder(),
                                       FastMath.rint(data[0]));
    }

    /** {@inheritDoc} */
    public long round() {
        return FastMath.round(data[0]);
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public DerivativeStructure signum() {
        return new DerivativeStructure(compiler.getFreeParameters(),
                                       compiler.getOrder(),
                                       FastMath.signum(data[0]));
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public DerivativeStructure copySign(final DerivativeStructure sign){
        long m = Double.doubleToLongBits(data[0]);
        long s = Double.doubleToLongBits(sign.data[0]);
        if ((m >= 0 && s >= 0) || (m < 0 && s < 0)) { // Sign is currently OK
            return this;
        }
        return negate(); // flip sign
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public DerivativeStructure copySign(final double sign) {
        long m = Double.doubleToLongBits(data[0]);
        long s = Double.doubleToLongBits(sign);
        if ((m >= 0 && s >= 0) || (m < 0 && s < 0)) { // Sign is currently OK
            return this;
        }
        return negate(); // flip sign
    }

    /**
     * Return the exponent of the instance value, removing the bias.
     * <p>
     * For double numbers of the form 2<sup>x</sup>, the unbiased
     * exponent is exactly x.
     * </p>
     * @return exponent for instance in IEEE754 representation, without bias
     */
    public int getExponent() {
        return FastMath.getExponent(data[0]);
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public DerivativeStructure scalb(final int n) {
        final DerivativeStructure ds = new DerivativeStructure(compiler);
        for (int i = 0; i < ds.data.length; ++i) {
            ds.data[i] = FastMath.scalb(data[i], n);
        }
        return ds;
    }

    /** {@inheritDoc}
     * @exception DimensionMismatchException if number of free parameters
     * or orders do not match
     * @since 3.2
     */
    public DerivativeStructure hypot(final DerivativeStructure y)
        throws DimensionMismatchException {

        compiler.checkCompatibility(y.compiler);

        if (Double.isInfinite(data[0]) || Double.isInfinite(y.data[0])) {
            return new DerivativeStructure(compiler.getFreeParameters(),
                                           compiler.getFreeParameters(),
                                           Double.POSITIVE_INFINITY);
        } else if (Double.isNaN(data[0]) || Double.isNaN(y.data[0])) {
            return new DerivativeStructure(compiler.getFreeParameters(),
                                           compiler.getFreeParameters(),
                                           Double.NaN);
        } else {

            final int expX = getExponent();
            final int expY = y.getExponent();
            if (expX > expY + 27) {
                // y is neglectible with respect to x
                return abs();
            } else if (expY > expX + 27) {
                // x is neglectible with respect to y
                return y.abs();
            } else {

                // find an intermediate scale to avoid both overflow and underflow
                final int middleExp = (expX + expY) / 2;

                // scale parameters without losing precision
                final DerivativeStructure scaledX = scalb(-middleExp);
                final DerivativeStructure scaledY = y.scalb(-middleExp);

                // compute scaled hypotenuse
                final DerivativeStructure scaledH =
                        scaledX.multiply(scaledX).add(scaledY.multiply(scaledY)).sqrt();

                // remove scaling
                return scaledH.scalb(middleExp);

            }

        }
    }

    /**
     * Returns the hypotenuse of a triangle with sides {@code x} and {@code y}
     * - sqrt(<i>x</i><sup>2</sup>&nbsp;+<i>y</i><sup>2</sup>)
     * avoiding intermediate overflow or underflow.
     *
     * <ul>
     * <li> If either argument is infinite, then the result is positive infinity.</li>
     * <li> else, if either argument is NaN then the result is NaN.</li>
     * </ul>
     *
     * @param x a value
     * @param y a value
     * @return sqrt(<i>x</i><sup>2</sup>&nbsp;+<i>y</i><sup>2</sup>)
     * @exception DimensionMismatchException if number of free parameters
     * or orders do not match
     * @since 3.2
     */
    public static DerivativeStructure hypot(final DerivativeStructure x, final DerivativeStructure y)
        throws DimensionMismatchException {
        return x.hypot(y);
    }

    /** Compute composition of the instance by a univariate function.
     * @param f array of value and derivatives of the function at
     * the current point (i.e. [f({@link #getValue()}),
     * f'({@link #getValue()}), f''({@link #getValue()})...]).
     * @return f(this)
     * @exception DimensionMismatchException if the number of derivatives
     * in the array is not equal to {@link #getOrder() order} + 1
     */
    public DerivativeStructure compose(final double ... f)
        throws DimensionMismatchException {
        if (f.length != getOrder() + 1) {
            throw new DimensionMismatchException(f.length, getOrder() + 1);
        }
        final DerivativeStructure result = new DerivativeStructure(compiler);
        compiler.compose(data, 0, f, result.data, 0);
        return result;
    }

    /** {@inheritDoc} */
    public DerivativeStructure reciprocal() {
        final DerivativeStructure result = new DerivativeStructure(compiler);
        compiler.pow(data, 0, -1, result.data, 0);
        return result;
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public DerivativeStructure sqrt() {
        return rootN(2);
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public DerivativeStructure cbrt() {
        return rootN(3);
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public DerivativeStructure rootN(final int n) {
        final DerivativeStructure result = new DerivativeStructure(compiler);
        compiler.rootN(data, 0, n, result.data, 0);
        return result;
    }

    /** {@inheritDoc} */
    public Field<DerivativeStructure> getField() {
        return new Field<DerivativeStructure>() {

            /** {@inheritDoc} */
            public DerivativeStructure getZero() {
                return new DerivativeStructure(compiler.getFreeParameters(), compiler.getOrder(), 0.0);
            }

            /** {@inheritDoc} */
            public DerivativeStructure getOne() {
                return new DerivativeStructure(compiler.getFreeParameters(), compiler.getOrder(), 1.0);
            }

            /** {@inheritDoc} */
            public Class<? extends FieldElement<DerivativeStructure>> getRuntimeClass() {
                return DerivativeStructure.class;
            }

        };
    }

    /** Compute a<sup>x</sup> where a is a double and x a {@link DerivativeStructure}
     * @param a number to exponentiate
     * @param x power to apply
     * @return a<sup>x</sup>
     * @since 3.3
     */
    public static DerivativeStructure pow(final double a, final DerivativeStructure x) {
        final DerivativeStructure result = new DerivativeStructure(x.compiler);
        x.compiler.pow(a, x.data, 0, result.data, 0);
        return result;
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public DerivativeStructure pow(final double p) {
        final DerivativeStructure result = new DerivativeStructure(compiler);
        compiler.pow(data, 0, p, result.data, 0);
        return result;
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public DerivativeStructure pow(final int n) {
        final DerivativeStructure result = new DerivativeStructure(compiler);
        compiler.pow(data, 0, n, result.data, 0);
        return result;
    }

    /** {@inheritDoc}
     * @exception DimensionMismatchException if number of free parameters
     * or orders do not match
     * @since 3.2
     */
    public DerivativeStructure pow(final DerivativeStructure e)
        throws DimensionMismatchException {
        compiler.checkCompatibility(e.compiler);
        final DerivativeStructure result = new DerivativeStructure(compiler);
        compiler.pow(data, 0, e.data, 0, result.data, 0);
        return result;
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public DerivativeStructure exp() {
        final DerivativeStructure result = new DerivativeStructure(compiler);
        compiler.exp(data, 0, result.data, 0);
        return result;
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public DerivativeStructure expm1() {
        final DerivativeStructure result = new DerivativeStructure(compiler);
        compiler.expm1(data, 0, result.data, 0);
        return result;
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public DerivativeStructure log() {
        final DerivativeStructure result = new DerivativeStructure(compiler);
        compiler.log(data, 0, result.data, 0);
        return result;
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public DerivativeStructure log1p() {
        final DerivativeStructure result = new DerivativeStructure(compiler);
        compiler.log1p(data, 0, result.data, 0);
        return result;
    }

    /** Base 10 logarithm.
     * @return base 10 logarithm of the instance
     */
    public DerivativeStructure log10() {
        final DerivativeStructure result = new DerivativeStructure(compiler);
        compiler.log10(data, 0, result.data, 0);
        return result;
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public DerivativeStructure cos() {
        final DerivativeStructure result = new DerivativeStructure(compiler);
        compiler.cos(data, 0, result.data, 0);
        return result;
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public DerivativeStructure sin() {
        final DerivativeStructure result = new DerivativeStructure(compiler);
        compiler.sin(data, 0, result.data, 0);
        return result;
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public DerivativeStructure tan() {
        final DerivativeStructure result = new DerivativeStructure(compiler);
        compiler.tan(data, 0, result.data, 0);
        return result;
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public DerivativeStructure acos() {
        final DerivativeStructure result = new DerivativeStructure(compiler);
        compiler.acos(data, 0, result.data, 0);
        return result;
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public DerivativeStructure asin() {
        final DerivativeStructure result = new DerivativeStructure(compiler);
        compiler.asin(data, 0, result.data, 0);
        return result;
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public DerivativeStructure atan() {
        final DerivativeStructure result = new DerivativeStructure(compiler);
        compiler.atan(data, 0, result.data, 0);
        return result;
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public DerivativeStructure atan2(final DerivativeStructure x)
        throws DimensionMismatchException {
        compiler.checkCompatibility(x.compiler);
        final DerivativeStructure result = new DerivativeStructure(compiler);
        compiler.atan2(data, 0, x.data, 0, result.data, 0);
        return result;
    }

    /** Two arguments arc tangent operation.
     * @param y first argument of the arc tangent
     * @param x second argument of the arc tangent
     * @return atan2(y, x)
     * @exception DimensionMismatchException if number of free parameters
     * or orders do not match
     * @since 3.2
     */
    public static DerivativeStructure atan2(final DerivativeStructure y, final DerivativeStructure x)
        throws DimensionMismatchException {
        return y.atan2(x);
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public DerivativeStructure cosh() {
        final DerivativeStructure result = new DerivativeStructure(compiler);
        compiler.cosh(data, 0, result.data, 0);
        return result;
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public DerivativeStructure sinh() {
        final DerivativeStructure result = new DerivativeStructure(compiler);
        compiler.sinh(data, 0, result.data, 0);
        return result;
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public DerivativeStructure tanh() {
        final DerivativeStructure result = new DerivativeStructure(compiler);
        compiler.tanh(data, 0, result.data, 0);
        return result;
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public DerivativeStructure acosh() {
        final DerivativeStructure result = new DerivativeStructure(compiler);
        compiler.acosh(data, 0, result.data, 0);
        return result;
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public DerivativeStructure asinh() {
        final DerivativeStructure result = new DerivativeStructure(compiler);
        compiler.asinh(data, 0, result.data, 0);
        return result;
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public DerivativeStructure atanh() {
        final DerivativeStructure result = new DerivativeStructure(compiler);
        compiler.atanh(data, 0, result.data, 0);
        return result;
    }

    /** Convert radians to degrees, with error of less than 0.5 ULP
     *  @return instance converted into degrees
     */
    public DerivativeStructure toDegrees() {
        final DerivativeStructure ds = new DerivativeStructure(compiler);
        for (int i = 0; i < ds.data.length; ++i) {
            ds.data[i] = FastMath.toDegrees(data[i]);
        }
        return ds;
    }

    /** Convert degrees to radians, with error of less than 0.5 ULP
     *  @return instance converted into radians
     */
    public DerivativeStructure toRadians() {
        final DerivativeStructure ds = new DerivativeStructure(compiler);
        for (int i = 0; i < ds.data.length; ++i) {
            ds.data[i] = FastMath.toRadians(data[i]);
        }
        return ds;
    }

    /** Evaluate Taylor expansion a derivative structure.
     * @param delta parameters offsets (&Delta;x, &Delta;y, ...)
     * @return value of the Taylor expansion at x + &Delta;x, y + &Delta;y, ...
     * @throws MathArithmeticException if factorials becomes too large
     */
    public double taylor(final double ... delta) throws MathArithmeticException {
        return compiler.taylor(data, 0, delta);
    }

    /** {@inheritDoc}
     * @exception DimensionMismatchException if number of free parameters
     * or orders do not match
     * @since 3.2
     */
    public DerivativeStructure linearCombination(final DerivativeStructure[] a, final DerivativeStructure[] b)
        throws DimensionMismatchException {

        // compute an accurate value, taking care of cancellations
        final double[] aDouble = new double[a.length];
        for (int i = 0; i < a.length; ++i) {
            aDouble[i] = a[i].getValue();
        }
        final double[] bDouble = new double[b.length];
        for (int i = 0; i < b.length; ++i) {
            bDouble[i] = b[i].getValue();
        }
        final double accurateValue = MathArrays.linearCombination(aDouble, bDouble);

        // compute a simple value, with all partial derivatives
        DerivativeStructure simpleValue = a[0].getField().getZero();
        for (int i = 0; i < a.length; ++i) {
            simpleValue = simpleValue.add(a[i].multiply(b[i]));
        }

        // create a result with accurate value and all derivatives (not necessarily as accurate as the value)
        final double[] all = simpleValue.getAllDerivatives();
        all[0] = accurateValue;
        return new DerivativeStructure(simpleValue.getFreeParameters(), simpleValue.getOrder(), all);

    }

    /** {@inheritDoc}
     * @exception DimensionMismatchException if number of free parameters
     * or orders do not match
     * @since 3.2
     */
    public DerivativeStructure linearCombination(final double[] a, final DerivativeStructure[] b)
        throws DimensionMismatchException {

        // compute an accurate value, taking care of cancellations
        final double[] bDouble = new double[b.length];
        for (int i = 0; i < b.length; ++i) {
            bDouble[i] = b[i].getValue();
        }
        final double accurateValue = MathArrays.linearCombination(a, bDouble);

        // compute a simple value, with all partial derivatives
        DerivativeStructure simpleValue = b[0].getField().getZero();
        for (int i = 0; i < a.length; ++i) {
            simpleValue = simpleValue.add(b[i].multiply(a[i]));
        }

        // create a result with accurate value and all derivatives (not necessarily as accurate as the value)
        final double[] all = simpleValue.getAllDerivatives();
        all[0] = accurateValue;
        return new DerivativeStructure(simpleValue.getFreeParameters(), simpleValue.getOrder(), all);

    }

    /** {@inheritDoc}
     * @exception DimensionMismatchException if number of free parameters
     * or orders do not match
     * @since 3.2
     */
    public DerivativeStructure linearCombination(final DerivativeStructure a1, final DerivativeStructure b1,
                                                 final DerivativeStructure a2, final DerivativeStructure b2)
        throws DimensionMismatchException {

        // compute an accurate value, taking care of cancellations
        final double accurateValue = MathArrays.linearCombination(a1.getValue(), b1.getValue(),
                                                                  a2.getValue(), b2.getValue());

        // compute a simple value, with all partial derivatives
        final DerivativeStructure simpleValue = a1.multiply(b1).add(a2.multiply(b2));

        // create a result with accurate value and all derivatives (not necessarily as accurate as the value)
        final double[] all = simpleValue.getAllDerivatives();
        all[0] = accurateValue;
        return new DerivativeStructure(getFreeParameters(), getOrder(), all);

    }

    /** {@inheritDoc}
     * @exception DimensionMismatchException if number of free parameters
     * or orders do not match
     * @since 3.2
     */
    public DerivativeStructure linearCombination(final double a1, final DerivativeStructure b1,
                                                 final double a2, final DerivativeStructure b2)
        throws DimensionMismatchException {

        // compute an accurate value, taking care of cancellations
        final double accurateValue = MathArrays.linearCombination(a1, b1.getValue(),
                                                                  a2, b2.getValue());

        // compute a simple value, with all partial derivatives
        final DerivativeStructure simpleValue = b1.multiply(a1).add(b2.multiply(a2));

        // create a result with accurate value and all derivatives (not necessarily as accurate as the value)
        final double[] all = simpleValue.getAllDerivatives();
        all[0] = accurateValue;
        return new DerivativeStructure(getFreeParameters(), getOrder(), all);

    }

    /** {@inheritDoc}
     * @exception DimensionMismatchException if number of free parameters
     * or orders do not match
     * @since 3.2
     */
    public DerivativeStructure linearCombination(final DerivativeStructure a1, final DerivativeStructure b1,
                                                 final DerivativeStructure a2, final DerivativeStructure b2,
                                                 final DerivativeStructure a3, final DerivativeStructure b3)
        throws DimensionMismatchException {

        // compute an accurate value, taking care of cancellations
        final double accurateValue = MathArrays.linearCombination(a1.getValue(), b1.getValue(),
                                                                  a2.getValue(), b2.getValue(),
                                                                  a3.getValue(), b3.getValue());

        // compute a simple value, with all partial derivatives
        final DerivativeStructure simpleValue = a1.multiply(b1).add(a2.multiply(b2)).add(a3.multiply(b3));

        // create a result with accurate value and all derivatives (not necessarily as accurate as the value)
        final double[] all = simpleValue.getAllDerivatives();
        all[0] = accurateValue;
        return new DerivativeStructure(getFreeParameters(), getOrder(), all);

    }

    /** {@inheritDoc}
     * @exception DimensionMismatchException if number of free parameters
     * or orders do not match
     * @since 3.2
     */
    public DerivativeStructure linearCombination(final double a1, final DerivativeStructure b1,
                                                 final double a2, final DerivativeStructure b2,
                                                 final double a3, final DerivativeStructure b3)
        throws DimensionMismatchException {

        // compute an accurate value, taking care of cancellations
        final double accurateValue = MathArrays.linearCombination(a1, b1.getValue(),
                                                                  a2, b2.getValue(),
                                                                  a3, b3.getValue());

        // compute a simple value, with all partial derivatives
        final DerivativeStructure simpleValue = b1.multiply(a1).add(b2.multiply(a2)).add(b3.multiply(a3));

        // create a result with accurate value and all derivatives (not necessarily as accurate as the value)
        final double[] all = simpleValue.getAllDerivatives();
        all[0] = accurateValue;
        return new DerivativeStructure(getFreeParameters(), getOrder(), all);

    }

    /** {@inheritDoc}
     * @exception DimensionMismatchException if number of free parameters
     * or orders do not match
     * @since 3.2
     */
    public DerivativeStructure linearCombination(final DerivativeStructure a1, final DerivativeStructure b1,
                                                 final DerivativeStructure a2, final DerivativeStructure b2,
                                                 final DerivativeStructure a3, final DerivativeStructure b3,
                                                 final DerivativeStructure a4, final DerivativeStructure b4)
        throws DimensionMismatchException {

        // compute an accurate value, taking care of cancellations
        final double accurateValue = MathArrays.linearCombination(a1.getValue(), b1.getValue(),
                                                                  a2.getValue(), b2.getValue(),
                                                                  a3.getValue(), b3.getValue(),
                                                                  a4.getValue(), b4.getValue());

        // compute a simple value, with all partial derivatives
        final DerivativeStructure simpleValue = a1.multiply(b1).add(a2.multiply(b2)).add(a3.multiply(b3)).add(a4.multiply(b4));

        // create a result with accurate value and all derivatives (not necessarily as accurate as the value)
        final double[] all = simpleValue.getAllDerivatives();
        all[0] = accurateValue;
        return new DerivativeStructure(getFreeParameters(), getOrder(), all);

    }

    /** {@inheritDoc}
     * @exception DimensionMismatchException if number of free parameters
     * or orders do not match
     * @since 3.2
     */
    public DerivativeStructure linearCombination(final double a1, final DerivativeStructure b1,
                                                 final double a2, final DerivativeStructure b2,
                                                 final double a3, final DerivativeStructure b3,
                                                 final double a4, final DerivativeStructure b4)
        throws DimensionMismatchException {

        // compute an accurate value, taking care of cancellations
        final double accurateValue = MathArrays.linearCombination(a1, b1.getValue(),
                                                                  a2, b2.getValue(),
                                                                  a3, b3.getValue(),
                                                                  a4, b4.getValue());

        // compute a simple value, with all partial derivatives
        final DerivativeStructure simpleValue = b1.multiply(a1).add(b2.multiply(a2)).add(b3.multiply(a3)).add(b4.multiply(a4));

        // create a result with accurate value and all derivatives (not necessarily as accurate as the value)
        final double[] all = simpleValue.getAllDerivatives();
        all[0] = accurateValue;
        return new DerivativeStructure(getFreeParameters(), getOrder(), all);

    }

    /**
     * Test for the equality of two derivative structures.
     * <p>
     * Derivative structures are considered equal if they have the same number
     * of free parameters, the same derivation order, and the same derivatives.
     * </p>
     * @param other Object to test for equality to this
     * @return true if two derivative structures are equal
     * @since 3.2
     */
    @Override
    public boolean equals(Object other) {

        if (this == other) {
            return true;
        }

        if (other instanceof DerivativeStructure) {
            final DerivativeStructure rhs = (DerivativeStructure)other;
            return (getFreeParameters() == rhs.getFreeParameters()) &&
                   (getOrder() == rhs.getOrder()) &&
                   MathArrays.equals(data, rhs.data);
        }

        return false;

    }

    /**
     * Get a hashCode for the derivative structure.
     * @return a hash code value for this object
     * @since 3.2
     */
    @Override
    public int hashCode() {
        return 227 + 229 * getFreeParameters() + 233 * getOrder() + 239 * MathUtils.hash(data);
    }

    /**
     * Replace the instance with a data transfer object for serialization.
     * @return data transfer object that will be serialized
     */
    private Object writeReplace() {
        return new DataTransferObject(compiler.getFreeParameters(), compiler.getOrder(), data);
    }

    /** Internal class used only for serialization. */
    private static class DataTransferObject implements Serializable {

        /** Serializable UID. */
        private static final long serialVersionUID = 20120730L;

        /** Number of variables.
         * @serial
         */
        private final int variables;

        /** Derivation order.
         * @serial
         */
        private final int order;

        /** Partial derivatives.
         * @serial
         */
        private final double[] data;

        /** Simple constructor.
         * @param variables number of variables
         * @param order derivation order
         * @param data partial derivatives
         */
        DataTransferObject(final int variables, final int order, final double[] data) {
            this.variables = variables;
            this.order     = order;
            this.data      = data;
        }

        /** Replace the deserialized data transfer object with a {@link DerivativeStructure}.
         * @return replacement {@link DerivativeStructure}
         */
        private Object readResolve() {
            return new DerivativeStructure(variables, order, data);
        }

    }

}
