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
package org.apache.commons.math3.geometry.euclidean.twod;

import java.text.NumberFormat;

import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.MathArithmeticException;
import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.geometry.Point;
import org.apache.commons.math3.geometry.Space;
import org.apache.commons.math3.geometry.Vector;
import org.apache.commons.math3.util.FastMath;
import org.apache.commons.math3.util.MathArrays;
import org.apache.commons.math3.util.MathUtils;

/** This class represents a 2D vector.
 * <p>Instances of this class are guaranteed to be immutable.</p>
 * @since 3.0
 */
public class Vector2D implements Vector<Euclidean2D> {

    /** Origin (coordinates: 0, 0). */
    public static final Vector2D ZERO   = new Vector2D(0, 0);

    // CHECKSTYLE: stop ConstantName
    /** A vector with all coordinates set to NaN. */
    public static final Vector2D NaN = new Vector2D(Double.NaN, Double.NaN);
    // CHECKSTYLE: resume ConstantName

    /** A vector with all coordinates set to positive infinity. */
    public static final Vector2D POSITIVE_INFINITY =
        new Vector2D(Double.POSITIVE_INFINITY, Double.POSITIVE_INFINITY);

    /** A vector with all coordinates set to negative infinity. */
    public static final Vector2D NEGATIVE_INFINITY =
        new Vector2D(Double.NEGATIVE_INFINITY, Double.NEGATIVE_INFINITY);

    /** Serializable UID. */
    private static final long serialVersionUID = 266938651998679754L;

    /** Abscissa. */
    private final double x;

    /** Ordinate. */
    private final double y;

    /** Simple constructor.
     * Build a vector from its coordinates
     * @param x abscissa
     * @param y ordinate
     * @see #getX()
     * @see #getY()
     */
    public Vector2D(double x, double y) {
        this.x = x;
        this.y = y;
    }

    /** Simple constructor.
     * Build a vector from its coordinates
     * @param v coordinates array
     * @exception DimensionMismatchException if array does not have 2 elements
     * @see #toArray()
     */
    public Vector2D(double[] v) throws DimensionMismatchException {
        if (v.length != 2) {
            throw new DimensionMismatchException(v.length, 2);
        }
        this.x = v[0];
        this.y = v[1];
    }

    /** Multiplicative constructor
     * Build a vector from another one and a scale factor.
     * The vector built will be a * u
     * @param a scale factor
     * @param u base (unscaled) vector
     */
    public Vector2D(double a, Vector2D u) {
        this.x = a * u.x;
        this.y = a * u.y;
    }

    /** Linear constructor
     * Build a vector from two other ones and corresponding scale factors.
     * The vector built will be a1 * u1 + a2 * u2
     * @param a1 first scale factor
     * @param u1 first base (unscaled) vector
     * @param a2 second scale factor
     * @param u2 second base (unscaled) vector
     */
    public Vector2D(double a1, Vector2D u1, double a2, Vector2D u2) {
        this.x = a1 * u1.x + a2 * u2.x;
        this.y = a1 * u1.y + a2 * u2.y;
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
    public Vector2D(double a1, Vector2D u1, double a2, Vector2D u2,
                   double a3, Vector2D u3) {
        this.x = a1 * u1.x + a2 * u2.x + a3 * u3.x;
        this.y = a1 * u1.y + a2 * u2.y + a3 * u3.y;
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
    public Vector2D(double a1, Vector2D u1, double a2, Vector2D u2,
                   double a3, Vector2D u3, double a4, Vector2D u4) {
        this.x = a1 * u1.x + a2 * u2.x + a3 * u3.x + a4 * u4.x;
        this.y = a1 * u1.y + a2 * u2.y + a3 * u3.y + a4 * u4.y;
    }

    /** Get the abscissa of the vector.
     * @return abscissa of the vector
     * @see #Vector2D(double, double)
     */
    public double getX() {
        return x;
    }

    /** Get the ordinate of the vector.
     * @return ordinate of the vector
     * @see #Vector2D(double, double)
     */
    public double getY() {
        return y;
    }

    /** Get the vector coordinates as a dimension 2 array.
     * @return vector coordinates
     * @see #Vector2D(double[])
     */
    public double[] toArray() {
        return new double[] { x, y };
    }

    /** {@inheritDoc} */
    public Space getSpace() {
        return Euclidean2D.getInstance();
    }

    /** {@inheritDoc} */
    public Vector2D getZero() {
        return ZERO;
    }

    /** {@inheritDoc} */
    public double getNorm1() {
        return FastMath.abs(x) + FastMath.abs(y);
    }

    /** {@inheritDoc} */
    public double getNorm() {
        return FastMath.sqrt (x * x + y * y);
    }

    /** {@inheritDoc} */
    public double getNormSq() {
        return x * x + y * y;
    }

    /** {@inheritDoc} */
    public double getNormInf() {
        return FastMath.max(FastMath.abs(x), FastMath.abs(y));
    }

    /** {@inheritDoc} */
    public Vector2D add(Vector<Euclidean2D> v) {
        Vector2D v2 = (Vector2D) v;
        return new Vector2D(x + v2.getX(), y + v2.getY());
    }

    /** {@inheritDoc} */
    public Vector2D add(double factor, Vector<Euclidean2D> v) {
        Vector2D v2 = (Vector2D) v;
        return new Vector2D(x + factor * v2.getX(), y + factor * v2.getY());
    }

    /** {@inheritDoc} */
    public Vector2D subtract(Vector<Euclidean2D> p) {
        Vector2D p3 = (Vector2D) p;
        return new Vector2D(x - p3.x, y - p3.y);
    }

    /** {@inheritDoc} */
    public Vector2D subtract(double factor, Vector<Euclidean2D> v) {
        Vector2D v2 = (Vector2D) v;
        return new Vector2D(x - factor * v2.getX(), y - factor * v2.getY());
    }

    /** {@inheritDoc} */
    public Vector2D normalize() throws MathArithmeticException {
        double s = getNorm();
        if (s == 0) {
            throw new MathArithmeticException(LocalizedFormats.CANNOT_NORMALIZE_A_ZERO_NORM_VECTOR);
        }
        return scalarMultiply(1 / s);
    }

    /** Compute the angular separation between two vectors.
     * <p>This method computes the angular separation between two
     * vectors using the dot product for well separated vectors and the
     * cross product for almost aligned vectors. This allows to have a
     * good accuracy in all cases, even for vectors very close to each
     * other.</p>
     * @param v1 first vector
     * @param v2 second vector
     * @return angular separation between v1 and v2
     * @exception MathArithmeticException if either vector has a null norm
     */
    public static double angle(Vector2D v1, Vector2D v2) throws MathArithmeticException {

        double normProduct = v1.getNorm() * v2.getNorm();
        if (normProduct == 0) {
            throw new MathArithmeticException(LocalizedFormats.ZERO_NORM);
        }

        double dot = v1.dotProduct(v2);
        double threshold = normProduct * 0.9999;
        if ((dot < -threshold) || (dot > threshold)) {
            // the vectors are almost aligned, compute using the sine
            final double n = FastMath.abs(MathArrays.linearCombination(v1.x, v2.y, -v1.y, v2.x));
            if (dot >= 0) {
                return FastMath.asin(n / normProduct);
            }
            return FastMath.PI - FastMath.asin(n / normProduct);
        }

        // the vectors are sufficiently separated to use the cosine
        return FastMath.acos(dot / normProduct);

    }

    /** {@inheritDoc} */
    public Vector2D negate() {
        return new Vector2D(-x, -y);
    }

    /** {@inheritDoc} */
    public Vector2D scalarMultiply(double a) {
        return new Vector2D(a * x, a * y);
    }

    /** {@inheritDoc} */
    public boolean isNaN() {
        return Double.isNaN(x) || Double.isNaN(y);
    }

    /** {@inheritDoc} */
    public boolean isInfinite() {
        return !isNaN() && (Double.isInfinite(x) || Double.isInfinite(y));
    }

    /** {@inheritDoc} */
    public double distance1(Vector<Euclidean2D> p) {
        Vector2D p3 = (Vector2D) p;
        final double dx = FastMath.abs(p3.x - x);
        final double dy = FastMath.abs(p3.y - y);
        return dx + dy;
    }

    /** {@inheritDoc}
     */
    public double distance(Vector<Euclidean2D> p) {
        return distance((Point<Euclidean2D>) p);
    }

    /** {@inheritDoc} */
    public double distance(Point<Euclidean2D> p) {
        Vector2D p3 = (Vector2D) p;
        final double dx = p3.x - x;
        final double dy = p3.y - y;
        return FastMath.sqrt(dx * dx + dy * dy);
    }

    /** {@inheritDoc} */
    public double distanceInf(Vector<Euclidean2D> p) {
        Vector2D p3 = (Vector2D) p;
        final double dx = FastMath.abs(p3.x - x);
        final double dy = FastMath.abs(p3.y - y);
        return FastMath.max(dx, dy);
    }

    /** {@inheritDoc} */
    public double distanceSq(Vector<Euclidean2D> p) {
        Vector2D p3 = (Vector2D) p;
        final double dx = p3.x - x;
        final double dy = p3.y - y;
        return dx * dx + dy * dy;
    }

    /** {@inheritDoc} */
    public double dotProduct(final Vector<Euclidean2D> v) {
        final Vector2D v2 = (Vector2D) v;
        return MathArrays.linearCombination(x, v2.x, y, v2.y);
    }

    /**
     * Compute the cross-product of the instance and the given points.
     * <p>
     * The cross product can be used to determine the location of a point
     * with regard to the line formed by (p1, p2) and is calculated as:
     * \[
     *    P = (x_2 - x_1)(y_3 - y_1) - (y_2 - y_1)(x_3 - x_1)
     * \]
     * with \(p3 = (x_3, y_3)\) being this instance.
     * <p>
     * If the result is 0, the points are collinear, i.e. lie on a single straight line L;
     * if it is positive, this point lies to the left, otherwise to the right of the line
     * formed by (p1, p2).
     *
     * @param p1 first point of the line
     * @param p2 second point of the line
     * @return the cross-product
     *
     * @see <a href="http://en.wikipedia.org/wiki/Cross_product">Cross product (Wikipedia)</a>
     */
    public double crossProduct(final Vector2D p1, final Vector2D p2) {
        final double x1 = p2.getX() - p1.getX();
        final double y1 = getY() - p1.getY();
        final double x2 = getX() - p1.getX();
        final double y2 = p2.getY() - p1.getY();
        return MathArrays.linearCombination(x1, y1, -x2, y2);
    }

    /** Compute the distance between two vectors according to the L<sub>2</sub> norm.
     * <p>Calling this method is equivalent to calling:
     * <code>p1.subtract(p2).getNorm()</code> except that no intermediate
     * vector is built</p>
     * @param p1 first vector
     * @param p2 second vector
     * @return the distance between p1 and p2 according to the L<sub>2</sub> norm
     */
    public static double distance(Vector2D p1, Vector2D p2) {
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
    public static double distanceInf(Vector2D p1, Vector2D p2) {
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
    public static double distanceSq(Vector2D p1, Vector2D p2) {
        return p1.distanceSq(p2);
    }

    /**
     * Test for the equality of two 2D vectors.
     * <p>
     * If all coordinates of two 2D vectors are exactly the same, and none are
     * <code>Double.NaN</code>, the two 2D vectors are considered to be equal.
     * </p>
     * <p>
     * <code>NaN</code> coordinates are considered to affect globally the vector
     * and be equals to each other - i.e, if either (or all) coordinates of the
     * 2D vector are equal to <code>Double.NaN</code>, the 2D vector is equal to
     * {@link #NaN}.
     * </p>
     *
     * @param other Object to test for equality to this
     * @return true if two 2D vector objects are equal, false if
     *         object is null, not an instance of Vector2D, or
     *         not equal to this Vector2D instance
     *
     */
    @Override
    public boolean equals(Object other) {

        if (this == other) {
            return true;
        }

        if (other instanceof Vector2D) {
            final Vector2D rhs = (Vector2D)other;
            if (rhs.isNaN()) {
                return this.isNaN();
            }

            return (x == rhs.x) && (y == rhs.y);
        }
        return false;
    }

    /**
     * Get a hashCode for the 2D vector.
     * <p>
     * All NaN values have the same hash code.</p>
     *
     * @return a hash code value for this object
     */
    @Override
    public int hashCode() {
        if (isNaN()) {
            return 542;
        }
        return 122 * (76 * MathUtils.hash(x) +  MathUtils.hash(y));
    }

    /** Get a string representation of this vector.
     * @return a string representation of this vector
     */
    @Override
    public String toString() {
        return Vector2DFormat.getInstance().format(this);
    }

    /** {@inheritDoc} */
    public String toString(final NumberFormat format) {
        return new Vector2DFormat(format).format(this);
    }

}
