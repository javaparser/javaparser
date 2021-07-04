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
package org.apache.commons.math3.geometry.euclidean.oned;

import java.text.NumberFormat;

import org.apache.commons.math3.exception.MathArithmeticException;
import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.geometry.Point;
import org.apache.commons.math3.geometry.Space;
import org.apache.commons.math3.geometry.Vector;
import org.apache.commons.math3.util.FastMath;
import org.apache.commons.math3.util.MathUtils;

/** This class represents a 1D vector.
 * <p>Instances of this class are guaranteed to be immutable.</p>
 * @since 3.0
 */
public class Vector1D implements Vector<Euclidean1D> {

    /** Origin (coordinates: 0). */
    public static final Vector1D ZERO = new Vector1D(0.0);

    /** Unit (coordinates: 1). */
    public static final Vector1D ONE  = new Vector1D(1.0);

    // CHECKSTYLE: stop ConstantName
    /** A vector with all coordinates set to NaN. */
    public static final Vector1D NaN = new Vector1D(Double.NaN);
    // CHECKSTYLE: resume ConstantName

    /** A vector with all coordinates set to positive infinity. */
    public static final Vector1D POSITIVE_INFINITY =
        new Vector1D(Double.POSITIVE_INFINITY);

    /** A vector with all coordinates set to negative infinity. */
    public static final Vector1D NEGATIVE_INFINITY =
        new Vector1D(Double.NEGATIVE_INFINITY);

    /** Serializable UID. */
    private static final long serialVersionUID = 7556674948671647925L;

    /** Abscissa. */
    private final double x;

    /** Simple constructor.
     * Build a vector from its coordinates
     * @param x abscissa
     * @see #getX()
     */
    public Vector1D(double x) {
        this.x = x;
    }

    /** Multiplicative constructor
     * Build a vector from another one and a scale factor.
     * The vector built will be a * u
     * @param a scale factor
     * @param u base (unscaled) vector
     */
    public Vector1D(double a, Vector1D u) {
        this.x = a * u.x;
    }

    /** Linear constructor
     * Build a vector from two other ones and corresponding scale factors.
     * The vector built will be a1 * u1 + a2 * u2
     * @param a1 first scale factor
     * @param u1 first base (unscaled) vector
     * @param a2 second scale factor
     * @param u2 second base (unscaled) vector
     */
    public Vector1D(double a1, Vector1D u1, double a2, Vector1D u2) {
        this.x = a1 * u1.x + a2 * u2.x;
    }

    /** Linear constructor
     * Build a vector from three other ones and corresponding scale factors.
     * The vector built will be a1 * u1 + a2 * u2 + a3 * u3
     * @param a1 first scale factor
     * @param u1 first base (unscaled) vector
     * @param a2 second scale factor
     * @param u2 second base (unscaled) vector
     * @param a3 third scale factor
     * @param u3 third base (unscaled) vector
     */
    public Vector1D(double a1, Vector1D u1, double a2, Vector1D u2,
                   double a3, Vector1D u3) {
        this.x = a1 * u1.x + a2 * u2.x + a3 * u3.x;
    }

    /** Linear constructor
     * Build a vector from four other ones and corresponding scale factors.
     * The vector built will be a1 * u1 + a2 * u2 + a3 * u3 + a4 * u4
     * @param a1 first scale factor
     * @param u1 first base (unscaled) vector
     * @param a2 second scale factor
     * @param u2 second base (unscaled) vector
     * @param a3 third scale factor
     * @param u3 third base (unscaled) vector
     * @param a4 fourth scale factor
     * @param u4 fourth base (unscaled) vector
     */
    public Vector1D(double a1, Vector1D u1, double a2, Vector1D u2,
                   double a3, Vector1D u3, double a4, Vector1D u4) {
        this.x = a1 * u1.x + a2 * u2.x + a3 * u3.x + a4 * u4.x;
    }

    /** Get the abscissa of the vector.
     * @return abscissa of the vector
     * @see #Vector1D(double)
     */
    public double getX() {
        return x;
    }

    /** {@inheritDoc} */
    public Space getSpace() {
        return Euclidean1D.getInstance();
    }

    /** {@inheritDoc} */
    public Vector1D getZero() {
        return ZERO;
    }

    /** {@inheritDoc} */
    public double getNorm1() {
        return FastMath.abs(x);
    }

    /** {@inheritDoc} */
    public double getNorm() {
        return FastMath.abs(x);
    }

    /** {@inheritDoc} */
    public double getNormSq() {
        return x * x;
    }

    /** {@inheritDoc} */
    public double getNormInf() {
        return FastMath.abs(x);
    }

    /** {@inheritDoc} */
    public Vector1D add(Vector<Euclidean1D> v) {
        Vector1D v1 = (Vector1D) v;
        return new Vector1D(x + v1.getX());
    }

    /** {@inheritDoc} */
    public Vector1D add(double factor, Vector<Euclidean1D> v) {
        Vector1D v1 = (Vector1D) v;
        return new Vector1D(x + factor * v1.getX());
    }

    /** {@inheritDoc} */
    public Vector1D subtract(Vector<Euclidean1D> p) {
        Vector1D p3 = (Vector1D) p;
        return new Vector1D(x - p3.x);
    }

    /** {@inheritDoc} */
    public Vector1D subtract(double factor, Vector<Euclidean1D> v) {
        Vector1D v1 = (Vector1D) v;
        return new Vector1D(x - factor * v1.getX());
    }

    /** {@inheritDoc} */
    public Vector1D normalize() throws MathArithmeticException {
        double s = getNorm();
        if (s == 0) {
            throw new MathArithmeticException(LocalizedFormats.CANNOT_NORMALIZE_A_ZERO_NORM_VECTOR);
        }
        return scalarMultiply(1 / s);
    }
    /** {@inheritDoc} */
    public Vector1D negate() {
        return new Vector1D(-x);
    }

    /** {@inheritDoc} */
    public Vector1D scalarMultiply(double a) {
        return new Vector1D(a * x);
    }

    /** {@inheritDoc} */
    public boolean isNaN() {
        return Double.isNaN(x);
    }

    /** {@inheritDoc} */
    public boolean isInfinite() {
        return !isNaN() && Double.isInfinite(x);
    }

    /** {@inheritDoc} */
    public double distance1(Vector<Euclidean1D> p) {
        Vector1D p3 = (Vector1D) p;
        final double dx = FastMath.abs(p3.x - x);
        return dx;
    }

    /** {@inheritDoc}
     * @deprecated as of 3.3, replaced with {@link #distance(Point)}
     */
    @Deprecated
    public double distance(Vector<Euclidean1D> p) {
        return distance((Point<Euclidean1D>) p);
    }

    /** {@inheritDoc} */
    public double distance(Point<Euclidean1D> p) {
        Vector1D p3 = (Vector1D) p;
        final double dx = p3.x - x;
        return FastMath.abs(dx);
    }

    /** {@inheritDoc} */
    public double distanceInf(Vector<Euclidean1D> p) {
        Vector1D p3 = (Vector1D) p;
        final double dx = FastMath.abs(p3.x - x);
        return dx;
    }

    /** {@inheritDoc} */
    public double distanceSq(Vector<Euclidean1D> p) {
        Vector1D p3 = (Vector1D) p;
        final double dx = p3.x - x;
        return dx * dx;
    }

    /** {@inheritDoc} */
    public double dotProduct(final Vector<Euclidean1D> v) {
        final Vector1D v1 = (Vector1D) v;
        return x * v1.x;
    }

    /** Compute the distance between two vectors according to the L<sub>2</sub> norm.
     * <p>Calling this method is equivalent to calling:
     * <code>p1.subtract(p2).getNorm()</code> except that no intermediate
     * vector is built</p>
     * @param p1 first vector
     * @param p2 second vector
     * @return the distance between p1 and p2 according to the L<sub>2</sub> norm
     */
    public static double distance(Vector1D p1, Vector1D p2) {
        return p1.distance(p2);
    }

    /** Compute the distance between two vectors according to the L<sub>&infin;</sub> norm.
     * <p>Calling this method is equivalent to calling:
     * <code>p1.subtract(p2).getNormInf()</code> except that no intermediate
     * vector is built</p>
     * @param p1 first vector
     * @param p2 second vector
     * @return the distance between p1 and p2 according to the L<sub>&infin;</sub> norm
     */
    public static double distanceInf(Vector1D p1, Vector1D p2) {
        return p1.distanceInf(p2);
    }

    /** Compute the square of the distance between two vectors.
     * <p>Calling this method is equivalent to calling:
     * <code>p1.subtract(p2).getNormSq()</code> except that no intermediate
     * vector is built</p>
     * @param p1 first vector
     * @param p2 second vector
     * @return the square of the distance between p1 and p2
     */
    public static double distanceSq(Vector1D p1, Vector1D p2) {
        return p1.distanceSq(p2);
    }

    /**
     * Test for the equality of two 1D vectors.
     * <p>
     * If all coordinates of two 1D vectors are exactly the same, and none are
     * <code>Double.NaN</code>, the two 1D vectors are considered to be equal.
     * </p>
     * <p>
     * <code>NaN</code> coordinates are considered to affect globally the vector
     * and be equals to each other - i.e, if either (or all) coordinates of the
     * 1D vector are equal to <code>Double.NaN</code>, the 1D vector is equal to
     * {@link #NaN}.
     * </p>
     *
     * @param other Object to test for equality to this
     * @return true if two 1D vector objects are equal, false if
     *         object is null, not an instance of Vector1D, or
     *         not equal to this Vector1D instance
     *
     */
    @Override
    public boolean equals(Object other) {

        if (this == other) {
            return true;
        }

        if (other instanceof Vector1D) {
            final Vector1D rhs = (Vector1D)other;
            if (rhs.isNaN()) {
                return this.isNaN();
            }

            return x == rhs.x;
        }
        return false;
    }

    /**
     * Get a hashCode for the 1D vector.
     * <p>
     * All NaN values have the same hash code.</p>
     *
     * @return a hash code value for this object
     */
    @Override
    public int hashCode() {
        if (isNaN()) {
            return 7785;
        }
        return 997 * MathUtils.hash(x);
    }

    /** Get a string representation of this vector.
     * @return a string representation of this vector
     */
    @Override
    public String toString() {
        return Vector1DFormat.getInstance().format(this);
    }

    /** {@inheritDoc} */
    public String toString(final NumberFormat format) {
        return new Vector1DFormat(format).format(this);
    }

}
