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
package org.apache.commons.math3.util;

import org.apache.commons.math3.RealFieldElement;
import org.apache.commons.math3.Field;
import org.apache.commons.math3.exception.DimensionMismatchException;

/**
 * This class wraps a {@code double} value in an object. It is similar to the
 * standard class {@link Double}, while also implementing the
 * {@link RealFieldElement} interface.
 *
 * @since 3.1
 */
public class Decimal64 extends Number
                       implements RealFieldElement<Decimal64>, Comparable<Decimal64> {

    /** The constant value of {@code 0d} as a {@code Decimal64}. */
    public static final Decimal64 ZERO;

    /** The constant value of {@code 1d} as a {@code Decimal64}. */
    public static final Decimal64 ONE;

    /**
     * The constant value of {@link Double#NEGATIVE_INFINITY} as a
     * {@code Decimal64}.
     */
    public static final Decimal64 NEGATIVE_INFINITY;

    /**
     * The constant value of {@link Double#POSITIVE_INFINITY} as a
     * {@code Decimal64}.
     */
    public static final Decimal64 POSITIVE_INFINITY;

    /** The constant value of {@link Double#NaN} as a {@code Decimal64}. */
    public static final Decimal64 NAN;

    /** */
    private static final long serialVersionUID = 20120227L;

    static {
        ZERO = new Decimal64(0d);
        ONE = new Decimal64(1d);
        NEGATIVE_INFINITY = new Decimal64(Double.NEGATIVE_INFINITY);
        POSITIVE_INFINITY = new Decimal64(Double.POSITIVE_INFINITY);
        NAN = new Decimal64(Double.NaN);
    }

    /** The primitive {@code double} value of this object. */
    private final double value;

    /**
     * Creates a new instance of this class.
     *
     * @param x the primitive {@code double} value of the object to be created
     */
    public Decimal64(final double x) {
        this.value = x;
    }

    /*
     * Methods from the FieldElement interface.
     */

    /** {@inheritDoc} */
    public Field<Decimal64> getField() {
        return Decimal64Field.getInstance();
    }

    /**
     * {@inheritDoc}
     *
     * The current implementation strictly enforces
     * {@code this.add(a).equals(new Decimal64(this.doubleValue()
     * + a.doubleValue()))}.
     */
    public Decimal64 add(final Decimal64 a) {
        return new Decimal64(this.value + a.value);
    }

    /**
     * {@inheritDoc}
     *
     * The current implementation strictly enforces
     * {@code this.subtract(a).equals(new Decimal64(this.doubleValue()
     * - a.doubleValue()))}.
     */
    public Decimal64 subtract(final Decimal64 a) {
        return new Decimal64(this.value - a.value);
    }

    /**
     * {@inheritDoc}
     *
     * The current implementation strictly enforces
     * {@code this.negate().equals(new Decimal64(-this.doubleValue()))}.
     */
    public Decimal64 negate() {
        return new Decimal64(-this.value);
    }

    /**
     * {@inheritDoc}
     *
     * The current implementation strictly enforces
     * {@code this.multiply(a).equals(new Decimal64(this.doubleValue()
     * * a.doubleValue()))}.
     */
    public Decimal64 multiply(final Decimal64 a) {
        return new Decimal64(this.value * a.value);
    }

    /**
     * {@inheritDoc}
     *
     * The current implementation strictly enforces
     * {@code this.multiply(n).equals(new Decimal64(n * this.doubleValue()))}.
     */
    public Decimal64 multiply(final int n) {
        return new Decimal64(n * this.value);
    }

    /**
     * {@inheritDoc}
     *
     * The current implementation strictly enforces
     * {@code this.divide(a).equals(new Decimal64(this.doubleValue()
     * / a.doubleValue()))}.
     *
     */
    public Decimal64 divide(final Decimal64 a) {
        return new Decimal64(this.value / a.value);
    }

    /**
     * {@inheritDoc}
     *
     * The current implementation strictly enforces
     * {@code this.reciprocal().equals(new Decimal64(1.0
     * / this.doubleValue()))}.
     */
    public Decimal64 reciprocal() {
        return new Decimal64(1.0 / this.value);
    }

    /*
     * Methods from the Number abstract class
     */

    /**
     * {@inheritDoc}
     *
     * The current implementation performs casting to a {@code byte}.
     */
    @Override
    public byte byteValue() {
        return (byte) value;
    }

    /**
     * {@inheritDoc}
     *
     * The current implementation performs casting to a {@code short}.
     */
    @Override
    public short shortValue() {
        return (short) value;
    }

    /**
     * {@inheritDoc}
     *
     * The current implementation performs casting to a {@code int}.
     */
    @Override
    public int intValue() {
        return (int) value;
    }

    /**
     * {@inheritDoc}
     *
     * The current implementation performs casting to a {@code long}.
     */
    @Override
    public long longValue() {
        return (long) value;
    }

    /**
     * {@inheritDoc}
     *
     * The current implementation performs casting to a {@code float}.
     */
    @Override
    public float floatValue() {
        return (float) value;
    }

    /** {@inheritDoc} */
    @Override
    public double doubleValue() {
        return value;
    }

    /*
     * Methods from the Comparable interface.
     */

    /**
     * {@inheritDoc}
     *
     * The current implementation returns the same value as
     * <center> {@code new Double(this.doubleValue()).compareTo(new
     * Double(o.doubleValue()))} </center>
     *
     * @see Double#compareTo(Double)
     */
    public int compareTo(final Decimal64 o) {
        return Double.compare(this.value, o.value);
    }

    /*
     * Methods from the Object abstract class.
     */

    /** {@inheritDoc} */
    @Override
    public boolean equals(final Object obj) {
        if (obj instanceof Decimal64) {
            final Decimal64 that = (Decimal64) obj;
            return Double.doubleToLongBits(this.value) == Double
                    .doubleToLongBits(that.value);
        }
        return false;
    }

    /**
     * {@inheritDoc}
     *
     * The current implementation returns the same value as
     * {@code new Double(this.doubleValue()).hashCode()}
     *
     * @see Double#hashCode()
     */
    @Override
    public int hashCode() {
        long v = Double.doubleToLongBits(value);
        return (int) (v ^ (v >>> 32));
    }

    /**
     * {@inheritDoc}
     *
     * The returned {@code String} is equal to
     * {@code Double.toString(this.doubleValue())}
     *
     * @see Double#toString(double)
     */
    @Override
    public String toString() {
        return Double.toString(value);
    }

    /*
     * Methods inspired by the Double class.
     */

    /**
     * Returns {@code true} if {@code this} double precision number is infinite
     * ({@link Double#POSITIVE_INFINITY} or {@link Double#NEGATIVE_INFINITY}).
     *
     * @return {@code true} if {@code this} number is infinite
     */
    public boolean isInfinite() {
        return Double.isInfinite(value);
    }

    /**
     * Returns {@code true} if {@code this} double precision number is
     * Not-a-Number ({@code NaN}), false otherwise.
     *
     * @return {@code true} if {@code this} is {@code NaN}
     */
    public boolean isNaN() {
        return Double.isNaN(value);
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public double getReal() {
        return value;
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public Decimal64 add(final double a) {
        return new Decimal64(value + a);
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public Decimal64 subtract(final double a) {
        return new Decimal64(value - a);
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public Decimal64 multiply(final double a) {
        return new Decimal64(value * a);
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public Decimal64 divide(final double a) {
        return new Decimal64(value / a);
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public Decimal64 remainder(final double a) {
        return new Decimal64(FastMath.IEEEremainder(value, a));
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public Decimal64 remainder(final Decimal64 a) {
        return new Decimal64(FastMath.IEEEremainder(value, a.value));
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public Decimal64 abs() {
        return new Decimal64(FastMath.abs(value));
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public Decimal64 ceil() {
        return new Decimal64(FastMath.ceil(value));
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public Decimal64 floor() {
        return new Decimal64(FastMath.floor(value));
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public Decimal64 rint() {
        return new Decimal64(FastMath.rint(value));
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public long round() {
        return FastMath.round(value);
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public Decimal64 signum() {
        return new Decimal64(FastMath.signum(value));
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public Decimal64 copySign(final Decimal64 sign) {
        return new Decimal64(FastMath.copySign(value, sign.value));
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public Decimal64 copySign(final double sign) {
        return new Decimal64(FastMath.copySign(value, sign));
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public Decimal64 scalb(final int n) {
        return new Decimal64(FastMath.scalb(value, n));
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public Decimal64 hypot(final Decimal64 y) {
        return new Decimal64(FastMath.hypot(value, y.value));
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public Decimal64 sqrt() {
        return new Decimal64(FastMath.sqrt(value));
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public Decimal64 cbrt() {
        return new Decimal64(FastMath.cbrt(value));
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public Decimal64 rootN(final int n) {
        if (value < 0) {
            return new Decimal64(-FastMath.pow(-value, 1.0 / n));
        } else {
            return new Decimal64(FastMath.pow(value, 1.0 / n));
        }
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public Decimal64 pow(final double p) {
        return new Decimal64(FastMath.pow(value, p));
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public Decimal64 pow(final int n) {
        return new Decimal64(FastMath.pow(value, n));
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public Decimal64 pow(final Decimal64 e) {
        return new Decimal64(FastMath.pow(value, e.value));
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public Decimal64 exp() {
        return new Decimal64(FastMath.exp(value));
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public Decimal64 expm1() {
        return new Decimal64(FastMath.expm1(value));
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public Decimal64 log() {
        return new Decimal64(FastMath.log(value));
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public Decimal64 log1p() {
        return new Decimal64(FastMath.log1p(value));
    }

    /** Base 10 logarithm.
     * @return base 10 logarithm of the instance
     * @since 3.2
     */
    public Decimal64 log10() {
        return new Decimal64(FastMath.log10(value));
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public Decimal64 cos() {
        return new Decimal64(FastMath.cos(value));
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public Decimal64 sin() {
        return new Decimal64(FastMath.sin(value));
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public Decimal64 tan() {
        return new Decimal64(FastMath.tan(value));
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public Decimal64 acos() {
        return new Decimal64(FastMath.acos(value));
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public Decimal64 asin() {
        return new Decimal64(FastMath.asin(value));
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public Decimal64 atan() {
        return new Decimal64(FastMath.atan(value));
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public Decimal64 atan2(final Decimal64 x) {
        return new Decimal64(FastMath.atan2(value, x.value));
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public Decimal64 cosh() {
        return new Decimal64(FastMath.cosh(value));
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public Decimal64 sinh() {
        return new Decimal64(FastMath.sinh(value));
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public Decimal64 tanh() {
        return new Decimal64(FastMath.tanh(value));
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public Decimal64 acosh() {
        return new Decimal64(FastMath.acosh(value));
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public Decimal64 asinh() {
        return new Decimal64(FastMath.asinh(value));
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public Decimal64 atanh() {
        return new Decimal64(FastMath.atanh(value));
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public Decimal64 linearCombination(final Decimal64[] a, final Decimal64[] b)
        throws DimensionMismatchException {
        if (a.length != b.length) {
            throw new DimensionMismatchException(a.length, b.length);
        }
        final double[] aDouble = new double[a.length];
        final double[] bDouble = new double[b.length];
        for (int i = 0; i < a.length; ++i) {
            aDouble[i] = a[i].value;
            bDouble[i] = b[i].value;
        }
        return new Decimal64(MathArrays.linearCombination(aDouble, bDouble));
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public Decimal64 linearCombination(final double[] a, final Decimal64[] b)
        throws DimensionMismatchException {
        if (a.length != b.length) {
            throw new DimensionMismatchException(a.length, b.length);
        }
        final double[] bDouble = new double[b.length];
        for (int i = 0; i < a.length; ++i) {
            bDouble[i] = b[i].value;
        }
        return new Decimal64(MathArrays.linearCombination(a, bDouble));
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public Decimal64 linearCombination(final Decimal64 a1, final Decimal64 b1,
                                       final Decimal64 a2, final Decimal64 b2) {
        return new Decimal64(MathArrays.linearCombination(a1.value, b1.value,
                                                          a2.value, b2.value));
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public Decimal64 linearCombination(final double a1, final Decimal64 b1,
                                       final double a2, final Decimal64 b2) {
        return new Decimal64(MathArrays.linearCombination(a1, b1.value,
                                                          a2, b2.value));
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public Decimal64 linearCombination(final Decimal64 a1, final Decimal64 b1,
                                       final Decimal64 a2, final Decimal64 b2,
                                       final Decimal64 a3, final Decimal64 b3) {
        return new Decimal64(MathArrays.linearCombination(a1.value, b1.value,
                                                          a2.value, b2.value,
                                                          a3.value, b3.value));
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public Decimal64 linearCombination(final double a1, final Decimal64 b1,
                                       final double a2, final Decimal64 b2,
                                       final double a3, final Decimal64 b3) {
        return new Decimal64(MathArrays.linearCombination(a1, b1.value,
                                                          a2, b2.value,
                                                          a3, b3.value));
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public Decimal64 linearCombination(final Decimal64 a1, final Decimal64 b1,
                                       final Decimal64 a2, final Decimal64 b2,
                                       final Decimal64 a3, final Decimal64 b3,
                                       final Decimal64 a4, final Decimal64 b4) {
        return new Decimal64(MathArrays.linearCombination(a1.value, b1.value,
                                                          a2.value, b2.value,
                                                          a3.value, b3.value,
                                                          a4.value, b4.value));
    }

    /** {@inheritDoc}
     * @since 3.2
     */
    public Decimal64 linearCombination(final double a1, final Decimal64 b1,
                                       final double a2, final Decimal64 b2,
                                       final double a3, final Decimal64 b3,
                                       final double a4, final Decimal64 b4) {
        return new Decimal64(MathArrays.linearCombination(a1, b1.value,
                                                          a2, b2.value,
                                                          a3, b3.value,
                                                          a4, b4.value));
    }

}
