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

import org.apache.commons.math3.geometry.Point;
import org.apache.commons.math3.geometry.euclidean.threed.Rotation;
import org.apache.commons.math3.geometry.euclidean.threed.Vector3D;
import org.apache.commons.math3.geometry.partitioning.Embedding;
import org.apache.commons.math3.geometry.partitioning.Hyperplane;
import org.apache.commons.math3.geometry.partitioning.SubHyperplane;
import org.apache.commons.math3.geometry.partitioning.Transform;
import org.apache.commons.math3.geometry.spherical.oned.Arc;
import org.apache.commons.math3.geometry.spherical.oned.ArcsSet;
import org.apache.commons.math3.geometry.spherical.oned.S1Point;
import org.apache.commons.math3.geometry.spherical.oned.Sphere1D;
import org.apache.commons.math3.util.FastMath;

/** This class represents an oriented great circle on the 2-sphere.

 * <p>An oriented circle can be defined by a center point. The circle
 * is the the set of points that are in the normal plan the center.</p>

 * <p>Since it is oriented the two spherical caps at its two sides are
 * unambiguously identified as a left cap and a right cap. This can be
 * used to identify the interior and the exterior in a simple way by
 * local properties only when part of a line is used to define part of
 * a spherical polygon boundary.</p>

 * @since 3.3
 */
public class Circle implements Hyperplane<Sphere2D>, Embedding<Sphere2D, Sphere1D> {

    /** Pole or circle center. */
    private Vector3D pole;

    /** First axis in the equator plane, origin of the phase angles. */
    private Vector3D x;

    /** Second axis in the equator plane, in quadrature with respect to x. */
    private Vector3D y;

    /** Tolerance below which close sub-arcs are merged together. */
    private final double tolerance;

    /** Build a great circle from its pole.
     * <p>The circle is oriented in the trigonometric direction around pole.</p>
     * @param pole circle pole
     * @param tolerance tolerance below which close sub-arcs are merged together
     */
    public Circle(final Vector3D pole, final double tolerance) {
        reset(pole);
        this.tolerance = tolerance;
    }

    /** Build a great circle from two non-aligned points.
     * <p>The circle is oriented from first to second point using the path smaller than \( \pi \).</p>
     * @param first first point contained in the great circle
     * @param second second point contained in the great circle
     * @param tolerance tolerance below which close sub-arcs are merged together
     */
    public Circle(final S2Point first, final S2Point second, final double tolerance) {
        reset(first.getVector().crossProduct(second.getVector()));
        this.tolerance = tolerance;
    }

    /** Build a circle from its internal components.
     * <p>The circle is oriented in the trigonometric direction around center.</p>
     * @param pole circle pole
     * @param x first axis in the equator plane
     * @param y second axis in the equator plane
     * @param tolerance tolerance below which close sub-arcs are merged together
     */
    private Circle(final Vector3D pole, final Vector3D x, final Vector3D y,
                   final double tolerance) {
        this.pole      = pole;
        this.x         = x;
        this.y         = y;
        this.tolerance = tolerance;
    }

    /** Copy constructor.
     * <p>The created instance is completely independent from the
     * original instance, it is a deep copy.</p>
     * @param circle circle to copy
     */
    public Circle(final Circle circle) {
        this(circle.pole, circle.x, circle.y, circle.tolerance);
    }

    /** {@inheritDoc} */
    public Circle copySelf() {
        return new Circle(this);
    }

    /** Reset the instance as if built from a pole.
     * <p>The circle is oriented in the trigonometric direction around pole.</p>
     * @param newPole circle pole
     */
    public void reset(final Vector3D newPole) {
        this.pole = newPole.normalize();
        this.x    = newPole.orthogonal();
        this.y    = Vector3D.crossProduct(newPole, x).normalize();
    }

    /** Revert the instance.
     */
    public void revertSelf() {
        // x remains the same
        y    = y.negate();
        pole = pole.negate();
    }

    /** Get the reverse of the instance.
     * <p>Get a circle with reversed orientation with respect to the
     * instance. A new object is built, the instance is untouched.</p>
     * @return a new circle, with orientation opposite to the instance orientation
     */
    public Circle getReverse() {
        return new Circle(pole.negate(), x, y.negate(), tolerance);
    }

    /** {@inheritDoc} */
    public Point<Sphere2D> project(Point<Sphere2D> point) {
        return toSpace(toSubSpace(point));
    }

    /** {@inheritDoc} */
    public double getTolerance() {
        return tolerance;
    }

    /** {@inheritDoc}
     * @see #getPhase(Vector3D)
     */
    public S1Point toSubSpace(final Point<Sphere2D> point) {
        return new S1Point(getPhase(((S2Point) point).getVector()));
    }

    /** Get the phase angle of a direction.
     * <p>
     * The direction may not belong to the circle as the
     * phase is computed for the meridian plane between the circle
     * pole and the direction.
     * </p>
     * @param direction direction for which phase is requested
     * @return phase angle of the direction around the circle
     * @see #toSubSpace(Point)
     */
    public double getPhase(final Vector3D direction) {
        return FastMath.PI + FastMath.atan2(-direction.dotProduct(y), -direction.dotProduct(x));
    }

    /** {@inheritDoc}
     * @see #getPointAt(double)
     */
    public S2Point toSpace(final Point<Sphere1D> point) {
        return new S2Point(getPointAt(((S1Point) point).getAlpha()));
    }

    /** Get a circle point from its phase around the circle.
     * @param alpha phase around the circle
     * @return circle point on the sphere
     * @see #toSpace(Point)
     * @see #getXAxis()
     * @see #getYAxis()
     */
    public Vector3D getPointAt(final double alpha) {
        return new Vector3D(FastMath.cos(alpha), x, FastMath.sin(alpha), y);
    }

    /** Get the X axis of the circle.
     * <p>
     * This method returns the same value as {@link #getPointAt(double)
     * getPointAt(0.0)} but it does not do any computation and always
     * return the same instance.
     * </p>
     * @return an arbitrary x axis on the circle
     * @see #getPointAt(double)
     * @see #getYAxis()
     * @see #getPole()
     */
    public Vector3D getXAxis() {
        return x;
    }

    /** Get the Y axis of the circle.
     * <p>
     * This method returns the same value as {@link #getPointAt(double)
     * getPointAt(0.5 * FastMath.PI)} but it does not do any computation and always
     * return the same instance.
     * </p>
     * @return an arbitrary y axis point on the circle
     * @see #getPointAt(double)
     * @see #getXAxis()
     * @see #getPole()
     */
    public Vector3D getYAxis() {
        return y;
    }

    /** Get the pole of the circle.
     * <p>
     * As the circle is a great circle, the pole does <em>not</em>
     * belong to it.
     * </p>
     * @return pole of the circle
     * @see #getXAxis()
     * @see #getYAxis()
     */
    public Vector3D getPole() {
        return pole;
    }

    /** Get the arc of the instance that lies inside the other circle.
     * @param other other circle
     * @return arc of the instance that lies inside the other circle
     */
    public Arc getInsideArc(final Circle other) {
        final double alpha  = getPhase(other.pole);
        final double halfPi = 0.5 * FastMath.PI;
        return new Arc(alpha - halfPi, alpha + halfPi, tolerance);
    }

    /** {@inheritDoc} */
    public SubCircle wholeHyperplane() {
        return new SubCircle(this, new ArcsSet(tolerance));
    }

    /** Build a region covering the whole space.
     * @return a region containing the instance (really a {@link
     * SphericalPolygonsSet SphericalPolygonsSet} instance)
     */
    public SphericalPolygonsSet wholeSpace() {
        return new SphericalPolygonsSet(tolerance);
    }

    /** {@inheritDoc}
     * @see #getOffset(Vector3D)
     */
    public double getOffset(final Point<Sphere2D> point) {
        return getOffset(((S2Point) point).getVector());
    }

    /** Get the offset (oriented distance) of a direction.
     * <p>The offset is defined as the angular distance between the
     * circle center and the direction minus the circle radius. It
     * is therefore 0 on the circle, positive for directions outside of
     * the cone delimited by the circle, and negative inside the cone.</p>
     * @param direction direction to check
     * @return offset of the direction
     * @see #getOffset(Point)
     */
    public double getOffset(final Vector3D direction) {
        return Vector3D.angle(pole, direction) - 0.5 * FastMath.PI;
    }

    /** {@inheritDoc} */
    public boolean sameOrientationAs(final Hyperplane<Sphere2D> other) {
        final Circle otherC = (Circle) other;
        return Vector3D.dotProduct(pole, otherC.pole) >= 0.0;
    }

    /** Get a {@link org.apache.commons.math3.geometry.partitioning.Transform
     * Transform} embedding a 3D rotation.
     * @param rotation rotation to use
     * @return a new transform that can be applied to either {@link
     * Point Point}, {@link Circle Line} or {@link
     * org.apache.commons.math3.geometry.partitioning.SubHyperplane
     * SubHyperplane} instances
     */
    public static Transform<Sphere2D, Sphere1D> getTransform(final Rotation rotation) {
        return new CircleTransform(rotation);
    }

    /** Class embedding a 3D rotation. */
    private static class CircleTransform implements Transform<Sphere2D, Sphere1D> {

        /** Underlying rotation. */
        private final Rotation rotation;

        /** Build a transform from a {@code Rotation}.
         * @param rotation rotation to use
         */
        CircleTransform(final Rotation rotation) {
            this.rotation = rotation;
        }

        /** {@inheritDoc} */
        public S2Point apply(final Point<Sphere2D> point) {
            return new S2Point(rotation.applyTo(((S2Point) point).getVector()));
        }

        /** {@inheritDoc} */
        public Circle apply(final Hyperplane<Sphere2D> hyperplane) {
            final Circle circle = (Circle) hyperplane;
            return new Circle(rotation.applyTo(circle.pole),
                              rotation.applyTo(circle.x),
                              rotation.applyTo(circle.y),
                              circle.tolerance);
        }

        /** {@inheritDoc} */
        public SubHyperplane<Sphere1D> apply(final SubHyperplane<Sphere1D> sub,
                                             final Hyperplane<Sphere2D> original,
                                             final Hyperplane<Sphere2D> transformed) {
            // as the circle is rotated, the limit angles are rotated too
            return sub;
        }

    }

}
