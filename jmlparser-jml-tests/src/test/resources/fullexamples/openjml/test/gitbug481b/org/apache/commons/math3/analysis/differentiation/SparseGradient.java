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
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

import org.apache.commons.math3.Field;
import org.apache.commons.math3.FieldElement;
import org.apache.commons.math3.RealFieldElement;
import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.util.FastMath;
import org.apache.commons.math3.util.MathArrays;
import org.apache.commons.math3.util.MathUtils;
import org.apache.commons.math3.util.Precision;

/**
 * First derivative computation with large number of variables.
 * <p>
 * This class plays a similar role to {@link DerivativeStructure}, with
 * a focus on efficiency when dealing with large number of independent variables
 * and most computation depend only on a few of them, and when only first derivative
 * is desired. When these conditions are met, this class should be much faster than
 * {@link DerivativeStructure} and use less memory.
 * </p>
 *
 * @since 3.3
 */
public class SparseGradient implements RealFieldElement<SparseGradient>, Serializable {

    /** Serializable UID. */
    private static final long serialVersionUID = 20131025L;

    /** Value of the calculation. */
    private double value;

    /** Stored derivative, each key representing a different independent variable. */
    private final Map<Integer, Double> derivatives;

    /** Internal constructor.
     * @param value value of the function
     * @param derivatives derivatives map, a deep copy will be performed,
     * so the map given here will remain safe from changes in the new instance,
     * may be null to create an empty derivatives map, i.e. a constant value
     */
    private SparseGradient(final double value, final Map<Integer, Double> derivatives) {
        this.value = value;
        this.derivatives = new HashMap<Integer, Double>();
        if (derivatives != null) {
            this.derivatives.putAll(derivatives);
        }
    }

    /** Internal constructor.
     * @param value value of the function
     * @param scale scaling factor to apply to all derivatives
     * @param derivatives derivatives map, a deep copy will be performed,
     * so the map given here will remain safe from changes in the new instance,
     * may be null to create an empty derivatives map, i.e. a constant value
     */
    private SparseGradient(final double value, final double scale,
                             final Map<Integer, Double> derivatives) {
        this.value = value;
        this.derivatives = new HashMap<Integer, Double>();
        if (derivatives != null) {
            for (final Map.Entry<Integer, Double> entry : derivatives.entrySet()) {
                this.derivatives.put(entry.getKey(), scale * entry.getValue());
            }
        }
    }

    /** Factory method creating a constant.
     * @param value value of the constant
     * @return a new instance
     */
    public static SparseGradient createConstant(final double value) {
        return new SparseGradient(value, Collections.<Integer, Double> emptyMap());
    }

    /** Factory method creating an independent variable.
     * @param idx index of the variable
     * @param value value of the variable
     * @return a new instance
     */
    public static SparseGradient createVariable(final int idx, final double value) {
        return new SparseGradient(value, Collections.singletonMap(idx, 1.0));
    }

    /**
     * Find the number of variables.
     * @return number of variables
     */
    public int numVars() {
        return derivatives.size();
    }

    /**
     * Get the derivative with respect to a particular index variable.
     *
     * @param index index to differentiate with.
     * @return derivative with respect to a particular index variable
     */
    public double getDerivative(final int index) {
        final Double out = derivatives.get(index);
        return (out == null) ? 0.0 : out;
    }

    /**
     * Get the value of the function.
     * @return value of the function.
     */
    public double getValue() {
        return value;
    }

    /** {@inheritDoc} */
    public double getReal() {
        return value;
    }

    /** {@inheritDoc} */
    public SparseGradient add(final SparseGradient a) {
        final SparseGradient out = new SparseGradient(value + a.value, derivatives);
        for (Map.Entry<Integer, Double> entry : a.derivatives.entrySet()) {
            final int id = entry.getKey();
            final Double old = out.derivatives.get(id);
            if (old == null) {
                out.derivatives.put(id, entry.getValue());
            } else {
                out.derivatives.put(id, old + entry.getValue());
            }
        }

        return out;
    }

    /**
     * Add in place.
     * <p>
     * This method is designed to be faster when used multiple times in a loop.
     * </p>
     * <p>
     * The instance is changed here, in order to not change the
     * instance the {@link #add(SparseGradient)} method should
     * be used.
     * </p>
     * @param a instance to add
     */
    public void addInPlace(final SparseGradient a) {
        value += a.value;
        for (final Map.Entry<Integer, Double> entry : a.derivatives.entrySet()) {
            final int id = entry.getKey();
            final Double old = derivatives.get(id);
            if (old == null) {
                derivatives.put(id, entry.getValue());
            } else {
                derivatives.put(id, old + entry.getValue());
            }
        }
    }

    /** {@inheritDoc} */
    public SparseGradient add(final double c) {
        final SparseGradient out = new SparseGradient(value + c, derivatives);
        return out;
    }

    /** {@inheritDoc} */
    public SparseGradient subtract(final SparseGradient a) {
        final SparseGradient out = new SparseGradient(value - a.value, derivatives);
        for (Map.Entry<Integer, Double> entry : a.derivatives.entrySet()) {
            final int id = entry.getKey();
            final Double old = out.derivatives.get(id);
            if (old == null) {
                out.derivatives.put(id, -entry.getValue());
            } else {
                out.derivatives.put(id, old - entry.getValue());
            }
        }
        return out;
    }

    /** {@inheritDoc} */
    public SparseGradient subtract(double c) {
        return new SparseGradient(value - c, derivatives);
    }

    /** {@inheritDoc} */
    public SparseGradient multiply(final SparseGradient a) {
        final SparseGradient out =
            new SparseGradient(value * a.value, Collections.<Integer, Double> emptyMap());

        // Derivatives.
        for (Map.Entry<Integer, Double> entry : derivatives.entrySet()) {
            out.derivatives.put(entry.getKey(), a.value * entry.getValue());
        }
        for (Map.Entry<Integer, Double> entry : a.derivatives.entrySet()) {
            final int id = entry.getKey();
            final Double old = out.derivatives.get(id);
            if (old == null) {
                out.derivatives.put(id, value * entry.getValue());
            } else {
                out.derivatives.put(id, old + value * entry.getValue());
            }
        }
        return out;
    }

    /**
     * Multiply in place.
     * <p>
     * This method is designed to be faster when used multiple times in a loop.
     * </p>
     * <p>
     * The instance is changed here, in order to not change the
     * instance the {@link #add(SparseGradient)} method should
     * be used.
     * </p>
     * @param a instance to multiply
     */
    public void multiplyInPlace(final SparseGradient a) {
        // Derivatives.
        for (Map.Entry<Integer, Double> entry : derivatives.entrySet()) {
            derivatives.put(entry.getKey(), a.value * entry.getValue());
        }
        for (Map.Entry<Integer, Double> entry : a.derivatives.entrySet()) {
            final int id = entry.getKey();
            final Double old = derivatives.get(id);
            if (old == null) {
                derivatives.put(id, value * entry.getValue());
            } else {
                derivatives.put(id, old + value * entry.getValue());
            }
        }
        value *= a.value;
    }

    /** {@inheritDoc} */
    public SparseGradient multiply(final double c) {
        return new SparseGradient(value * c, c, derivatives);
    }

    /** {@inheritDoc} */
    public SparseGradient multiply(final int n) {
        return new SparseGradient(value * n, n, derivatives);
    }

    /** {@inheritDoc} */
    public SparseGradient divide(final SparseGradient a) {
        final SparseGradient out = new SparseGradient(value / a.value, Collections.<Integer, Double> emptyMap());

        // Derivatives.
        for (Map.Entry<Integer, Double> entry : derivatives.entrySet()) {
            out.derivatives.put(entry.getKey(), entry.getValue() / a.value);
        }
        for (Map.Entry<Integer, Double> entry : a.derivatives.entrySet()) {
            final int id = entry.getKey();
            final Double old = out.derivatives.get(id);
            if (old == null) {
                out.derivatives.put(id, -out.value / a.value * entry.getValue());
            } else {
                out.derivatives.put(id, old - out.value / a.value * entry.getValue());
            }
        }
        return out;
    }

    /** {@inheritDoc} */
    public SparseGradient divide(final double c) {
        return new SparseGradient(value / c, 1.0 / c, derivatives);
    }

    /** {@inheritDoc} */
    public SparseGradient negate() {
        return new SparseGradient(-value, -1.0, derivatives);
    }

    /** {@inheritDoc} */
    public Field<SparseGradient> getField() {
        return new Field<SparseGradient>() {

            /** {@inheritDoc} */
            public SparseGradient getZero() {
                return createConstant(0);
            }

            /** {@inheritDoc} */
            public SparseGradient getOne() {
                return createConstant(1);
            }

            /** {@inheritDoc} */
            public Class<? extends FieldElement<SparseGradient>> getRuntimeClass() {
                return SparseGradient.class;
            }

        };
    }

    /** {@inheritDoc} */
    public SparseGradient remainder(final double a) {
        return new SparseGradient(FastMath.IEEEremainder(value, a), derivatives);
    }

    /** {@inheritDoc} */
    public SparseGradient remainder(final SparseGradient a) {

        // compute k such that lhs % rhs = lhs - k rhs
        final double rem = FastMath.IEEEremainder(value, a.value);
        final double k   = FastMath.rint((value - rem) / a.value);

        return subtract(a.multiply(k));

    }

    /** {@inheritDoc} */
    public SparseGradient abs() {
        if (Double.doubleToLongBits(value) < 0) {
            // we use the bits representation to also handle -0.0
            return negate();
        } else {
            return this;
        }
    }

    /** {@inheritDoc} */
    public SparseGradient ceil() {
        return createConstant(FastMath.ceil(value));
    }

    /** {@inheritDoc} */
    public SparseGradient floor() {
        return createConstant(FastMath.floor(value));
    }

    /** {@inheritDoc} */
    public SparseGradient rint() {
        return createConstant(FastMath.rint(value));
    }

    /** {@inheritDoc} */
    public long round() {
        return FastMath.round(value);
    }

    /** {@inheritDoc} */
    public SparseGradient signum() {
        return createConstant(FastMath.signum(value));
    }

    /** {@inheritDoc} */
    public SparseGradient copySign(final SparseGradient sign) {
        final long m = Double.doubleToLongBits(value);
        final long s = Double.doubleToLongBits(sign.value);
        if ((m >= 0 && s >= 0) || (m < 0 && s < 0)) { // Sign is currently OK
            return this;
        }
        return negate(); // flip sign
    }

    /** {@inheritDoc} */
    public SparseGradient copySign(final double sign) {
        final long m = Double.doubleToLongBits(value);
        final long s = Double.doubleToLongBits(sign);
        if ((m >= 0 && s >= 0) || (m < 0 && s < 0)) { // Sign is currently OK
            return this;
        }
        return negate(); // flip sign
    }

    /** {@inheritDoc} */
    public SparseGradient scalb(final int n) {
        final SparseGradient out = new SparseGradient(FastMath.scalb(value, n), Collections.<Integer, Double> emptyMap());
        for (Map.Entry<Integer, Double> entry : derivatives.entrySet()) {
            out.derivatives.put(entry.getKey(), FastMath.scalb(entry.getValue(), n));
        }
        return out;
    }

    /** {@inheritDoc} */
    public SparseGradient hypot(final SparseGradient y) {
        if (Double.isInfinite(value) || Double.isInfinite(y.value)) {
            return createConstant(Double.POSITIVE_INFINITY);
        } else if (Double.isNaN(value) || Double.isNaN(y.value)) {
            return createConstant(Double.NaN);
        } else {

            final int expX = FastMath.getExponent(value);
            final int expY = FastMath.getExponent(y.value);
            if (expX > expY + 27) {
                // y is negligible with respect to x
                return abs();
            } else if (expY > expX + 27) {
                // x is negligible with respect to y
                return y.abs();
            } else {

                // find an intermediate scale to avoid both overflow and underflow
                final int middleExp = (expX + expY) / 2;

                // scale parameters without losing precision
                final SparseGradient scaledX = scalb(-middleExp);
                final SparseGradient scaledY = y.scalb(-middleExp);

                // compute scaled hypotenuse
                final SparseGradient scaledH =
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
     */
    public static SparseGradient hypot(final SparseGradient x, final SparseGradient y) {
        return x.hypot(y);
    }

    /** {@inheritDoc} */
    public SparseGradient reciprocal() {
        return new SparseGradient(1.0 / value, -1.0 / (value * value), derivatives);
    }

    /** {@inheritDoc} */
    public SparseGradient sqrt() {
        final double sqrt = FastMath.sqrt(value);
        return new SparseGradient(sqrt, 0.5 / sqrt, derivatives);
    }

    /** {@inheritDoc} */
    public SparseGradient cbrt() {
        final double cbrt = FastMath.cbrt(value);
        return new SparseGradient(cbrt, 1.0 / (3 * cbrt * cbrt), derivatives);
    }

    /** {@inheritDoc} */
    public SparseGradient rootN(final int n) {
        if (n == 2) {
            return sqrt();
        } else if (n == 3) {
            return cbrt();
        } else {
            final double root = FastMath.pow(value, 1.0 / n);
            return new SparseGradient(root, 1.0 / (n * FastMath.pow(root, n - 1)), derivatives);
        }
    }

    /** {@inheritDoc} */
    public SparseGradient pow(final double p) {
        return new SparseGradient(FastMath.pow(value,  p), p * FastMath.pow(value,  p - 1), derivatives);
    }

    /** {@inheritDoc} */
    public SparseGradient pow(final int n) {
        if (n == 0) {
            return getField().getOne();
        } else {
            final double valueNm1 = FastMath.pow(value,  n - 1);
            return new SparseGradient(value * valueNm1, n * valueNm1, derivatives);
        }
    }

    /** {@inheritDoc} */
    public SparseGradient pow(final SparseGradient e) {
        return log().multiply(e).exp();
    }

    /** Compute a<sup>x</sup> where a is a double and x a {@link SparseGradient}
     * @param a number to exponentiate
     * @param x power to apply
     * @return a<sup>x</sup>
     */
    public static SparseGradient pow(final double a, final SparseGradient x) {
        if (a == 0) {
            if (x.value == 0) {
                return x.compose(1.0, Double.NEGATIVE_INFINITY);
            } else if (x.value < 0) {
                return x.compose(Double.NaN, Double.NaN);
            } else {
                return x.getField().getZero();
            }
        } else {
            final double ax = FastMath.pow(a, x.value);
            return new SparseGradient(ax, ax * FastMath.log(a), x.derivatives);
        }
    }

    /** {@inheritDoc} */
    public SparseGradient exp() {
        final double e = FastMath.exp(value);
        return new SparseGradient(e, e, derivatives);
    }

    /** {@inheritDoc} */
    public SparseGradient expm1() {
        return new SparseGradient(FastMath.expm1(value), FastMath.exp(value), derivatives);
    }

    /** {@inheritDoc} */
    public SparseGradient log() {
        return new SparseGradient(FastMath.log(value), 1.0 / value, derivatives);
    }

    /** Base 10 logarithm.
     * @return base 10 logarithm of the instance
     */
    public SparseGradient log10() {
        return new SparseGradient(FastMath.log10(value), 1.0 / (FastMath.log(10.0) * value), derivatives);
    }

    /** {@inheritDoc} */
    public SparseGradient log1p() {
        return new SparseGradient(FastMath.log1p(value), 1.0 / (1.0 + value), derivatives);
    }

    /** {@inheritDoc} */
    public SparseGradient cos() {
        return new SparseGradient(FastMath.cos(value), -FastMath.sin(value), derivatives);
    }

    /** {@inheritDoc} */
    public SparseGradient sin() {
        return new SparseGradient(FastMath.sin(value), FastMath.cos(value), derivatives);
    }

    /** {@inheritDoc} */
    public SparseGradient tan() {
        final double t = FastMath.tan(value);
        return new SparseGradient(t, 1 + t * t, derivatives);
    }

    /** {@inheritDoc} */
    public SparseGradient acos() {
        return new SparseGradient(FastMath.acos(value), -1.0 / FastMath.sqrt(1 - value * value), derivatives);
    }

    /** {@inheritDoc} */
    public SparseGradient asin() {
        return new SparseGradient(FastMath.asin(value), 1.0 / FastMath.sqrt(1 - value * value), derivatives);
    }

    /** {@inheritDoc} */
    public SparseGradient atan() {
        return new SparseGradient(FastMath.atan(value), 1.0 / (1 + value * value), derivatives);
    }

    /** {@inheritDoc} */
    public SparseGradient atan2(final SparseGradient x) {

        // compute r = sqrt(x^2+y^2)
        final SparseGradient r = multiply(this).add(x.multiply(x)).sqrt();

        final SparseGradient a;
        if (x.value >= 0) {

            // compute atan2(y, x) = 2 atan(y / (r + x))
            a = divide(r.add(x)).atan().multiply(2);

        } else {

            // compute atan2(y, x) = +/- pi - 2 atan(y / (r - x))
            final SparseGradient tmp = divide(r.subtract(x)).atan().multiply(-2);
            a = tmp.add(tmp.value <= 0 ? -FastMath.PI : FastMath.PI);

        }

        // fix value to take special cases (+0/+0, +0/-0, -0/+0, -0/-0, +/-infinity) correctly
        a.value = FastMath.atan2(value, x.value);

        return a;

    }

    /** Two arguments arc tangent operation.
     * @param y first argument of the arc tangent
     * @param x second argument of the arc tangent
     * @return atan2(y, x)
     */
    public static SparseGradient atan2(final SparseGradient y, final SparseGradient x) {
        return y.atan2(x);
    }

    /** {@inheritDoc} */
    public SparseGradient cosh() {
        return new SparseGradient(FastMath.cosh(value), FastMath.sinh(value), derivatives);
    }

    /** {@inheritDoc} */
    public SparseGradient sinh() {
        return new SparseGradient(FastMath.sinh(value), FastMath.cosh(value), derivatives);
    }

    /** {@inheritDoc} */
    public SparseGradient tanh() {
        final double t = FastMath.tanh(value);
        return new SparseGradient(t, 1 - t * t, derivatives);
    }

    /** {@inheritDoc} */
    public SparseGradient acosh() {
        return new SparseGradient(FastMath.acosh(value), 1.0 / FastMath.sqrt(value * value - 1.0), derivatives);
    }

    /** {@inheritDoc} */
    public SparseGradient asinh() {
        return new SparseGradient(FastMath.asinh(value), 1.0 / FastMath.sqrt(value * value + 1.0), derivatives);
    }

    /** {@inheritDoc} */
    public SparseGradient atanh() {
        return new SparseGradient(FastMath.atanh(value), 1.0 / (1.0 - value * value), derivatives);
    }

    /** Convert radians to degrees, with error of less than 0.5 ULP
     *  @return instance converted into degrees
     */
    public SparseGradient toDegrees() {
        return new SparseGradient(FastMath.toDegrees(value), FastMath.toDegrees(1.0), derivatives);
    }

    /** Convert degrees to radians, with error of less than 0.5 ULP
     *  @return instance converted into radians
     */
    public SparseGradient toRadians() {
        return new SparseGradient(FastMath.toRadians(value), FastMath.toRadians(1.0), derivatives);
    }

    /** Evaluate Taylor expansion of a sparse gradient.
     * @param delta parameters offsets (&Delta;x, &Delta;y, ...)
     * @return value of the Taylor expansion at x + &Delta;x, y + &Delta;y, ...
     */
    public double taylor(final double ... delta) {
        double y = value;
        for (int i = 0; i < delta.length; ++i) {
            y += delta[i] * getDerivative(i);
        }
        return y;
    }

    /** Compute composition of the instance by a univariate function.
     * @param f0 value of the function at (i.e. f({@link #getValue()}))
     * @param f1 first derivative of the function at
     * the current point (i.e. f'({@link #getValue()}))
     * @return f(this)
    */
    public SparseGradient compose(final double f0, final double f1) {
        return new SparseGradient(f0, f1, derivatives);
    }

    /** {@inheritDoc} */
    public SparseGradient linearCombination(final SparseGradient[] a,
                                              final SparseGradient[] b)
        throws DimensionMismatchException {

        // compute a simple value, with all partial derivatives
        SparseGradient out = a[0].getField().getZero();
        for (int i = 0; i < a.length; ++i) {
            out = out.add(a[i].multiply(b[i]));
        }

        // recompute an accurate value, taking care of cancellations
        final double[] aDouble = new double[a.length];
        for (int i = 0; i < a.length; ++i) {
            aDouble[i] = a[i].getValue();
        }
        final double[] bDouble = new double[b.length];
        for (int i = 0; i < b.length; ++i) {
            bDouble[i] = b[i].getValue();
        }
        out.value = MathArrays.linearCombination(aDouble, bDouble);

        return out;

    }

    /** {@inheritDoc} */
    public SparseGradient linearCombination(final double[] a, final SparseGradient[] b) {

        // compute a simple value, with all partial derivatives
        SparseGradient out = b[0].getField().getZero();
        for (int i = 0; i < a.length; ++i) {
            out = out.add(b[i].multiply(a[i]));
        }

        // recompute an accurate value, taking care of cancellations
        final double[] bDouble = new double[b.length];
        for (int i = 0; i < b.length; ++i) {
            bDouble[i] = b[i].getValue();
        }
        out.value = MathArrays.linearCombination(a, bDouble);

        return out;

    }

    /** {@inheritDoc} */
    public SparseGradient linearCombination(final SparseGradient a1, final SparseGradient b1,
                                              final SparseGradient a2, final SparseGradient b2) {

        // compute a simple value, with all partial derivatives
        SparseGradient out = a1.multiply(b1).add(a2.multiply(b2));

        // recompute an accurate value, taking care of cancellations
        out.value = MathArrays.linearCombination(a1.value, b1.value, a2.value, b2.value);

        return out;

    }

    /** {@inheritDoc} */
    public SparseGradient linearCombination(final double a1, final SparseGradient b1,
                                              final double a2, final SparseGradient b2) {

        // compute a simple value, with all partial derivatives
        SparseGradient out = b1.multiply(a1).add(b2.multiply(a2));

        // recompute an accurate value, taking care of cancellations
        out.value = MathArrays.linearCombination(a1, b1.value, a2, b2.value);

        return out;

    }

    /** {@inheritDoc} */
    public SparseGradient linearCombination(final SparseGradient a1, final SparseGradient b1,
                                              final SparseGradient a2, final SparseGradient b2,
                                              final SparseGradient a3, final SparseGradient b3) {

        // compute a simple value, with all partial derivatives
        SparseGradient out = a1.multiply(b1).add(a2.multiply(b2)).add(a3.multiply(b3));

        // recompute an accurate value, taking care of cancellations
        out.value = MathArrays.linearCombination(a1.value, b1.value,
                                                 a2.value, b2.value,
                                                 a3.value, b3.value);

        return out;

    }

    /** {@inheritDoc} */
    public SparseGradient linearCombination(final double a1, final SparseGradient b1,
                                              final double a2, final SparseGradient b2,
                                              final double a3, final SparseGradient b3) {

        // compute a simple value, with all partial derivatives
        SparseGradient out = b1.multiply(a1).add(b2.multiply(a2)).add(b3.multiply(a3));

        // recompute an accurate value, taking care of cancellations
        out.value = MathArrays.linearCombination(a1, b1.value,
                                                 a2, b2.value,
                                                 a3, b3.value);

        return out;

    }

    /** {@inheritDoc} */
    public SparseGradient linearCombination(final SparseGradient a1, final SparseGradient b1,
                                              final SparseGradient a2, final SparseGradient b2,
                                              final SparseGradient a3, final SparseGradient b3,
                                              final SparseGradient a4, final SparseGradient b4) {

        // compute a simple value, with all partial derivatives
        SparseGradient out = a1.multiply(b1).add(a2.multiply(b2)).add(a3.multiply(b3)).add(a4.multiply(b4));

        // recompute an accurate value, taking care of cancellations
        out.value = MathArrays.linearCombination(a1.value, b1.value,
                                                 a2.value, b2.value,
                                                 a3.value, b3.value,
                                                 a4.value, b4.value);

        return out;

    }

    /** {@inheritDoc} */
    public SparseGradient linearCombination(final double a1, final SparseGradient b1,
                                              final double a2, final SparseGradient b2,
                                              final double a3, final SparseGradient b3,
                                              final double a4, final SparseGradient b4) {

        // compute a simple value, with all partial derivatives
        SparseGradient out = b1.multiply(a1).add(b2.multiply(a2)).add(b3.multiply(a3)).add(b4.multiply(a4));

        // recompute an accurate value, taking care of cancellations
        out.value = MathArrays.linearCombination(a1, b1.value,
                                                 a2, b2.value,
                                                 a3, b3.value,
                                                 a4, b4.value);

        return out;

    }

    /**
     * Test for the equality of two sparse gradients.
     * <p>
     * Sparse gradients are considered equal if they have the same value
     * and the same derivatives.
     * </p>
     * @param other Object to test for equality to this
     * @return true if two sparse gradients are equal
     */
    @Override
    public boolean equals(Object other) {

        if (this == other) {
            return true;
        }

        if (other instanceof SparseGradient) {
            final SparseGradient rhs = (SparseGradient)other;
            if (!Precision.equals(value, rhs.value, 1)) {
                return false;
            }
            if (derivatives.size() != rhs.derivatives.size()) {
                return false;
            }
            for (final Map.Entry<Integer, Double> entry : derivatives.entrySet()) {
                if (!rhs.derivatives.containsKey(entry.getKey())) {
                    return false;
                }
                if (!Precision.equals(entry.getValue(), rhs.derivatives.get(entry.getKey()), 1)) {
                    return false;
                }
            }
            return true;
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
        return 743 + 809 * MathUtils.hash(value) + 167 * derivatives.hashCode();
    }

}
