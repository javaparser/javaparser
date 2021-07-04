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
package org.apache.commons.math3.geometry.spherical.oned;

import org.apache.commons.math3.geometry.Point;
import org.apache.commons.math3.geometry.partitioning.Hyperplane;

/** This class represents a 1D oriented hyperplane on the circle.
 * <p>An hyperplane on the 1-sphere is an angle with an orientation.</p>
 * <p>Instances of this class are guaranteed to be immutable.</p>
 * @since 3.3
 */
public class LimitAngle implements Hyperplane<Sphere1D> {

    /** Angle location. */
    private S1Point location;

    /** Orientation. */
    private boolean direct;

    /** Tolerance below which angles are considered identical. */
    private final double tolerance;

    /** Simple constructor.
     * @param location location of the hyperplane
     * @param direct if true, the plus side of the hyperplane is towards
     * angles greater than {@code location}
     * @param tolerance tolerance below which angles are considered identical
     */
    public LimitAngle(final S1Point location, final boolean direct, final double tolerance) {
        this.location  = location;
        this.direct    = direct;
        this.tolerance = tolerance;
    }

    /** Copy the instance.
     * <p>Since instances are immutable, this method directly returns
     * the instance.</p>
     * @return the instance itself
     */
    public LimitAngle copySelf() {
        return this;
    }

    /** {@inheritDoc} */
    public double getOffset(final Point<Sphere1D> point) {
        final double delta = ((S1Point) point).getAlpha() - location.getAlpha();
        return direct ? delta : -delta;
    }

    /** Check if the hyperplane orientation is direct.
     * @return true if the plus side of the hyperplane is towards
     * angles greater than hyperplane location
     */
    public boolean isDirect() {
        return direct;
    }

    /** Get the reverse of the instance.
     * <p>Get a limit angle with reversed orientation with respect to the
     * instance. A new object is built, the instance is untouched.</p>
     * @return a new limit angle, with orientation opposite to the instance orientation
     */
    public LimitAngle getReverse() {
        return new LimitAngle(location, !direct, tolerance);
    }

    /** Build a region covering the whole hyperplane.
     * <p>Since this class represent zero dimension spaces which does
     * not have lower dimension sub-spaces, this method returns a dummy
     * implementation of a {@link
     * org.apache.commons.math3.geometry.partitioning.SubHyperplane SubHyperplane}.
     * This implementation is only used to allow the {@link
     * org.apache.commons.math3.geometry.partitioning.SubHyperplane
     * SubHyperplane} class implementation to work properly, it should
     * <em>not</em> be used otherwise.</p>
     * @return a dummy sub hyperplane
     */
    public SubLimitAngle wholeHyperplane() {
        return new SubLimitAngle(this, null);
    }

    /** Build a region covering the whole space.
     * @return a region containing the instance (really an {@link
     * ArcsSet IntervalsSet} instance)
     */
    public ArcsSet wholeSpace() {
        return new ArcsSet(tolerance);
    }

    /** {@inheritDoc} */
    public boolean sameOrientationAs(final Hyperplane<Sphere1D> other) {
        return !(direct ^ ((LimitAngle) other).direct);
    }

    /** Get the hyperplane location on the circle.
     * @return the hyperplane location
     */
    public S1Point getLocation() {
        return location;
    }

    /** {@inheritDoc} */
    public Point<Sphere1D> project(Point<Sphere1D> point) {
        return location;
    }

    /** {@inheritDoc} */
    public double getTolerance() {
        return tolerance;
    }

}
