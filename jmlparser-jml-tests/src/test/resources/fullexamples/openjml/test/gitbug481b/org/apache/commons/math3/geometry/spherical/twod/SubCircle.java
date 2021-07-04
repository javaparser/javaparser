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

import org.apache.commons.math3.geometry.euclidean.threed.Vector3D;
import org.apache.commons.math3.geometry.partitioning.AbstractSubHyperplane;
import org.apache.commons.math3.geometry.partitioning.Hyperplane;
import org.apache.commons.math3.geometry.partitioning.Region;
import org.apache.commons.math3.geometry.spherical.oned.Arc;
import org.apache.commons.math3.geometry.spherical.oned.ArcsSet;
import org.apache.commons.math3.geometry.spherical.oned.Sphere1D;
import org.apache.commons.math3.util.FastMath;

/** This class represents a sub-hyperplane for {@link Circle}.
 * @since 3.3
 */
public class SubCircle extends AbstractSubHyperplane<Sphere2D, Sphere1D> {

    /** Simple constructor.
     * @param hyperplane underlying hyperplane
     * @param remainingRegion remaining region of the hyperplane
     */
    public SubCircle(final Hyperplane<Sphere2D> hyperplane,
                     final Region<Sphere1D> remainingRegion) {
        super(hyperplane, remainingRegion);
    }

    /** {@inheritDoc} */
    @Override
    protected AbstractSubHyperplane<Sphere2D, Sphere1D> buildNew(final Hyperplane<Sphere2D> hyperplane,
                                                                 final Region<Sphere1D> remainingRegion) {
        return new SubCircle(hyperplane, remainingRegion);
    }

    /** {@inheritDoc} */
    @Override
    public SplitSubHyperplane<Sphere2D> split(final Hyperplane<Sphere2D> hyperplane) {

        final Circle thisCircle   = (Circle) getHyperplane();
        final Circle otherCircle  = (Circle) hyperplane;
        final double angle = Vector3D.angle(thisCircle.getPole(), otherCircle.getPole());

        if (angle < thisCircle.getTolerance() || angle > FastMath.PI - thisCircle.getTolerance()) {
            // the two circles are aligned or opposite
            return new SplitSubHyperplane<Sphere2D>(null, null);
        } else {
            // the two circles intersect each other
            final Arc    arc          = thisCircle.getInsideArc(otherCircle);
            final ArcsSet.Split split = ((ArcsSet) getRemainingRegion()).split(arc);
            final ArcsSet plus        = split.getPlus();
            final ArcsSet minus       = split.getMinus();
            return new SplitSubHyperplane<Sphere2D>(plus  == null ? null : new SubCircle(thisCircle.copySelf(), plus),
                                                    minus == null ? null : new SubCircle(thisCircle.copySelf(), minus));
        }

    }

}
