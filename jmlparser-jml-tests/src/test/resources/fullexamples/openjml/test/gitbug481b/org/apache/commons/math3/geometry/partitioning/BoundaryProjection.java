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
package org.apache.commons.math3.geometry.partitioning;

import org.apache.commons.math3.geometry.Point;
import org.apache.commons.math3.geometry.Space;

/** Class holding the result of point projection on region boundary.
 * <p>This class is a simple placeholder, it does not provide any
 * processing methods.</p>
 * <p>Instances of this class are guaranteed to be immutable</p>
 * @param <S> Type of the space.
 * @since 3.3
 * @see AbstractRegion#projectToBoundary(Point)
 */
public class BoundaryProjection<S extends Space> {

    /** Original point. */
    private final Point<S> original;

    /** Projected point. */
    private final Point<S> projected;

    /** Offset of the point with respect to the boundary it is projected on. */
    private final double offset;

    /** Constructor from raw elements.
     * @param original original point
     * @param projected projected point
     * @param offset offset of the point with respect to the boundary it is projected on
     */
    public BoundaryProjection(final Point<S> original, final Point<S> projected, final double offset) {
        this.original  = original;
        this.projected = projected;
        this.offset    = offset;
    }

    /** Get the original point.
     * @return original point
     */
    public Point<S> getOriginal() {
        return original;
    }

    /** Projected point.
     * @return projected point, or null if there are no boundary
     */
    public Point<S> getProjected() {
        return projected;
    }

    /** Offset of the point with respect to the boundary it is projected on.
     * <p>
     * The offset with respect to the boundary is negative if the {@link
     * #getOriginal() original point} is inside the region, and positive otherwise.
     * </p>
     * <p>
     * If there are no boundary, the value is set to either {@code
     * Double.POSITIVE_INFINITY} if the region is empty (i.e. all points are
     * outside of the region) or {@code Double.NEGATIVE_INFINITY} if the region
     * covers the whole space (i.e. all points are inside of the region).
     * </p>
     * @return offset of the point with respect to the boundary it is projected on
     */
    public double getOffset() {
        return offset;
    }

}
