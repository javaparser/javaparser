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

import org.apache.commons.math3.geometry.partitioning.AbstractSubHyperplane;
import org.apache.commons.math3.geometry.partitioning.Hyperplane;
import org.apache.commons.math3.geometry.partitioning.Region;

/** This class represents sub-hyperplane for {@link OrientedPoint}.
 * <p>An hyperplane in 1D is a simple point, its orientation being a
 * boolean.</p>
 * <p>Instances of this class are guaranteed to be immutable.</p>
 * @since 3.0
 */
public class SubOrientedPoint extends AbstractSubHyperplane<Euclidean1D, Euclidean1D> {

    /** Simple constructor.
     * @param hyperplane underlying hyperplane
     * @param remainingRegion remaining region of the hyperplane
     */
    public SubOrientedPoint(final Hyperplane<Euclidean1D> hyperplane,
                            final Region<Euclidean1D> remainingRegion) {
        super(hyperplane, remainingRegion);
    }

    /** {@inheritDoc} */
    @Override
    public double getSize() {
        return 0;
    }

    /** {@inheritDoc} */
    @Override
    public boolean isEmpty() {
        return false;
    }

    /** {@inheritDoc} */
    @Override
    protected AbstractSubHyperplane<Euclidean1D, Euclidean1D> buildNew(final Hyperplane<Euclidean1D> hyperplane,
                                                                       final Region<Euclidean1D> remainingRegion) {
        return new SubOrientedPoint(hyperplane, remainingRegion);
    }

    /** {@inheritDoc} */
    @Override
    public SplitSubHyperplane<Euclidean1D> split(final Hyperplane<Euclidean1D> hyperplane) {
        final double global = hyperplane.getOffset(((OrientedPoint) getHyperplane()).getLocation());
        if (global < -1.0e-10) {
            return new SplitSubHyperplane<Euclidean1D>(null, this);
        } else if (global > 1.0e-10) {
            return new SplitSubHyperplane<Euclidean1D>(this, null);
        } else {
            return new SplitSubHyperplane<Euclidean1D>(null, null);
        }
    }

}
