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
package org.apache.commons.math3.geometry.spherical.twod;

import org.apache.commons.math3.exception.MathArithmeticException;
import org.apache.commons.math3.exception.OutOfRangeException;
import org.apache.commons.math3.geometry.Point;
import org.apache.commons.math3.geometry.Space;
import org.apache.commons.math3.geometry.euclidean.threed.Vector3D;
import org.apache.commons.math3.util.FastMath;
import org.apache.commons.math3.util.MathUtils;

/** This class represents a point on the 2-sphere.
 * <p>
 * We use the mathematical convention to use the azimuthal angle \( \theta \)
 * in the x-y plane as the first coordinate, and the polar angle \( \varphi \)
 * as the second coordinate (see <a
 * href="http://mathworld.wolfram.com/SphericalCoordinates.html">Spherical
 * Coordinates</a> in MathWorld).
 * </p>
 * <p>Instances of this class are guaranteed to be immutable.</p>
 * @since 3.3
 */
public class S2Point implements Point<Sphere2D> {

    /** +I (coordinates: \( \theta = 0, \varphi = \pi/2 \)). */
    public static final S2Point PLUS_I = new S2Point(0, 0.5 * FastMath.PI, Vector3D.PLUS_I);

    /** +J (coordinates: \( \theta = \pi/2, \varphi = \pi/2 \))). */
    public static final S2Point PLUS_J = new S2Point(0.5 * FastMath.PI, 0.5 * FastMath.PI, Vector3D.PLUS_J);

    /** +K (coordinates: \( \theta = any angle, \varphi = 0 \)). */
    public static final S2Point PLUS_K = new S2Point(0, 0, Vector3D.PLUS_K);

    /** -I (coordinates: \( \theta = \pi, \varphi = \pi/2 \)). */
    public static final S2Point MINUS_I = new S2Point(FastMath.PI, 0.5 * FastMath.PI, Vector3D.MINUS_I);

    /** -J (coordinates: \( \theta = 3\pi/2, \varphi = \pi/2 \)). */
    public static final S2Point MINUS_J = new S2Point(1.5 * FastMath.PI, 0.5 * FastMath.PI, Vector3D.MINUS_J);

    /** -K (coordinates: \( \theta = any angle, \varphi = \pi \)). */
    public static final S2Point MINUS_K = new S2Point(0, FastMath.PI, Vector3D.MINUS_K);

    // CHECKSTYLE: stop ConstantName
    /** A vector with all coordinates set to NaN. */
    public static final S2Point NaN = new S2Point(Double.NaN, Double.NaN, Vector3D.NaN);
    // CHECKSTYLE: resume ConstantName

    /** Serializable UID. */
    private static final long serialVersionUID = 20131218L;

    /** Azimuthal angle \( \theta \) in the x-y plane. */
    private final double theta;

    /** Polar angle \( \varphi \). */
    private final double phi;

    /** Corresponding 3D normalized vector. */
    private final Vector3D vector;

    /** Simple constructor.
     * Build a vector from its spherical coordinates
     * @param theta azimuthal angle \( \theta \) in the x-y plane
     * @param phi polar angle \( \varphi \)
     * @see #getTheta()
     * @see #getPhi()
     * @exception OutOfRangeException if \( \varphi \) is not in the [\( 0; \pi \)] range
     */
    public S2Point(final double theta, final double phi)
        throws OutOfRangeException {
        this(theta, phi, vector(theta, phi));
    }

    /** Simple constructor.
     * Build a vector from its underlying 3D vector
     * @param vector 3D vector
     * @exception MathArithmeticException if vector norm is zero
     */
    public S2Point(final Vector3D vector) throws MathArithmeticException {
        this(FastMath.atan2(vector.getY(), vector.getX()), Vector3D.angle(Vector3D.PLUS_K, vector),
             vector.normalize());
    }

    /** Build a point from its internal components.
     * @param theta azimuthal angle \( \theta \) in the x-y plane
     * @param phi polar angle \( \varphi \)
     * @param vector corresponding vector
     */
    private S2Point(final double theta, final double phi, final Vector3D vector) {
        this.theta  = theta;
        this.phi    = phi;
        this.vector = vector;
    }

    /** Build the normalized vector corresponding to spherical coordinates.
     * @param theta azimuthal angle \( \theta \) in the x-y plane
     * @param phi polar angle \( \varphi \)
     * @return normalized vector
     * @exception OutOfRangeException if \( \varphi \) is not in the [\( 0; \pi \)] range
     */
    private static Vector3D vector(final double theta, final double phi)
       throws OutOfRangeException {

        if (phi < 0 || phi > FastMath.PI) {
            throw new OutOfRangeException(phi, 0, FastMath.PI);
        }

        final double cosTheta = FastMath.cos(theta);
        final double sinTheta = FastMath.sin(theta);
        final double cosPhi   = FastMath.cos(phi);
        final double sinPhi   = FastMath.sin(phi);

        return new Vector3D(cosTheta * sinPhi, sinTheta * sinPhi, cosPhi);

    }

    /** Get the azimuthal angle \( \theta \) in the x-y plane.
     * @return azimuthal angle \( \theta \) in the x-y plane
     * @see #S2Point(double, double)
     */
    public double getTheta() {
        return theta;
    }

    /** Get the polar angle \( \varphi \).
     * @return polar angle \( \varphi \)
     * @see #S2Point(double, double)
     */
    public double getPhi() {
        return phi;
    }

    /** Get the corresponding normalized vector in the 3D euclidean space.
     * @return normalized vector
     */
    public Vector3D getVector() {
        return vector;
    }

    /** {@inheritDoc} */
    public Space getSpace() {
        return Sphere2D.getInstance();
    }

    /** {@inheritDoc} */
    public boolean isNaN() {
        return Double.isNaN(theta) || Double.isNaN(phi);
    }

    /** Get the opposite of the instance.
     * @return a new vector which is opposite to the instance
     */
    public S2Point negate() {
        return new S2Point(-theta, FastMath.PI - phi, vector.negate());
    }

    /** {@inheritDoc} */
    public double distance(final Point<Sphere2D> point) {
        return distance(this, (S2Point) point);
    }

    /** Compute the distance (angular separation) between two points.
     * @param p1 first vector
     * @param p2 second vector
     * @return the angular separation between p1 and p2
     */
    public static double distance(S2Point p1, S2Point p2) {
        return Vector3D.angle(p1.vector, p2.vector);
    }

    /**
     * Test for the equality of two points on the 2-sphere.
     * <p>
     * If all coordinates of two points are exactly the same, and none are
     * <code>Double.NaN</code>, the two points are considered to be equal.
     * </p>
     * <p>
     * <code>NaN</code> coordinates are considered to affect globally the vector
     * and be equals to each other - i.e, if either (or all) coordinates of the
     * 2D vector are equal to <code>Double.NaN</code>, the 2D vector is equal to
     * {@link #NaN}.
     * </p>
     *
     * @param other Object to test for equality to this
     * @return true if two points on the 2-sphere objects are equal, false if
     *         object is null, not an instance of S2Point, or
     *         not equal to this S2Point instance
     *
     */
    @Override
    public boolean equals(Object other) {

        if (this == other) {
            return true;
        }

        if (other instanceof S2Point) {
            final S2Point rhs = (S2Point) other;
            if (rhs.isNaN()) {
                return this.isNaN();
            }

            return (theta == rhs.theta) && (phi == rhs.phi);
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
        return 134 * (37 * MathUtils.hash(theta) +  MathUtils.hash(phi));
    }

}
