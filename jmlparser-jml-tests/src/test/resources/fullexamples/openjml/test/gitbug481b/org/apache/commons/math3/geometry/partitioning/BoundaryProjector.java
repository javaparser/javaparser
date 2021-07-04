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

import java.util.ArrayList;
import java.util.List;

import org.apache.commons.math3.geometry.Point;
import org.apache.commons.math3.geometry.Space;
import org.apache.commons.math3.geometry.partitioning.Region.Location;
import org.apache.commons.math3.util.FastMath;

/** Local tree visitor to compute projection on boundary.
 * @param <S> Type of the space.
 * @param <T> Type of the sub-space.
 * @since 3.3
 */
class BoundaryProjector<S extends Space, T extends Space> implements BSPTreeVisitor<S> {

    /** Original point. */
    private final Point<S> original;

    /** Current best projected point. */
    private Point<S> projected;

    /** Leaf node closest to the test point. */
    private BSPTree<S> leaf;

    /** Current offset. */
    private double offset;

    /** Simple constructor.
     * @param original original point
     */
    BoundaryProjector(final Point<S> original) {
        this.original  = original;
        this.projected = null;
        this.leaf      = null;
        this.offset    = Double.POSITIVE_INFINITY;
    }

    /** {@inheritDoc} */
    public Order visitOrder(final BSPTree<S> node) {
        // we want to visit the tree so that the first encountered
        // leaf is the one closest to the test point
        if (node.getCut().getHyperplane().getOffset(original) <= 0) {
            return Order.MINUS_SUB_PLUS;
        } else {
            return Order.PLUS_SUB_MINUS;
        }
    }

    /** {@inheritDoc} */
    public void visitInternalNode(final BSPTree<S> node) {

        // project the point on the cut sub-hyperplane
        final Hyperplane<S> hyperplane = node.getCut().getHyperplane();
        final double signedOffset = hyperplane.getOffset(original);
        if (FastMath.abs(signedOffset) < offset) {

            // project point
            final Point<S> regular = hyperplane.project(original);

            // get boundary parts
            final List<Region<T>> boundaryParts = boundaryRegions(node);

            // check if regular projection really belongs to the boundary
            boolean regularFound = false;
            for (final Region<T> part : boundaryParts) {
                if (!regularFound && belongsToPart(regular, hyperplane, part)) {
                    // the projected point lies in the boundary
                    projected    = regular;
                    offset       = FastMath.abs(signedOffset);
                    regularFound = true;
                }
            }

            if (!regularFound) {
                // the regular projected point is not on boundary,
                // so we have to check further if a singular point
                // (i.e. a vertex in 2D case) is a possible projection
                for (final Region<T> part : boundaryParts) {
                    final Point<S> spI = singularProjection(regular, hyperplane, part);
                    if (spI != null) {
                        final double distance = original.distance(spI);
                        if (distance < offset) {
                            projected = spI;
                            offset    = distance;
                        }
                    }
                }

            }

        }

    }

    /** {@inheritDoc} */
    public void visitLeafNode(final BSPTree<S> node) {
        if (leaf == null) {
            // this is the first leaf we visit,
            // it is the closest one to the original point
            leaf = node;
        }
    }

    /** Get the projection.
     * @return projection
     */
    public BoundaryProjection<S> getProjection() {

        // fix offset sign
        offset = FastMath.copySign(offset, (Boolean) leaf.getAttribute() ? -1 : +1);

        return new BoundaryProjection<S>(original, projected, offset);

    }

    /** Extract the regions of the boundary on an internal node.
     * @param node internal node
     * @return regions in the node sub-hyperplane
     */
    private List<Region<T>> boundaryRegions(final BSPTree<S> node) {

        final List<Region<T>> regions = new ArrayList<Region<T>>(2);

        @SuppressWarnings("unchecked")
        final BoundaryAttribute<S> ba = (BoundaryAttribute<S>) node.getAttribute();
        addRegion(ba.getPlusInside(),  regions);
        addRegion(ba.getPlusOutside(), regions);

        return regions;

    }

    /** Add a boundary region to a list.
     * @param sub sub-hyperplane defining the region
     * @param list to fill up
     */
    private void addRegion(final SubHyperplane<S> sub, final List<Region<T>> list) {
        if (sub != null) {
            @SuppressWarnings("unchecked")
            final Region<T> region = ((AbstractSubHyperplane<S, T>) sub).getRemainingRegion();
            if (region != null) {
                list.add(region);
            }
        }
    }

    /** Check if a projected point lies on a boundary part.
     * @param point projected point to check
     * @param hyperplane hyperplane into which the point was projected
     * @param part boundary part
     * @return true if point lies on the boundary part
     */
    private boolean belongsToPart(final Point<S> point, final Hyperplane<S> hyperplane,
                                  final Region<T> part) {

        // there is a non-null sub-space, we can dive into smaller dimensions
        @SuppressWarnings("unchecked")
        final Embedding<S, T> embedding = (Embedding<S, T>) hyperplane;
        return part.checkPoint(embedding.toSubSpace(point)) != Location.OUTSIDE;

    }

    /** Get the projection to the closest boundary singular point.
     * @param point projected point to check
     * @param hyperplane hyperplane into which the point was projected
     * @param part boundary part
     * @return projection to a singular point of boundary part (may be null)
     */
    private Point<S> singularProjection(final Point<S> point, final Hyperplane<S> hyperplane,
                                        final Region<T> part) {

        // there is a non-null sub-space, we can dive into smaller dimensions
        @SuppressWarnings("unchecked")
        final Embedding<S, T> embedding = (Embedding<S, T>) hyperplane;
        final BoundaryProjection<T> bp = part.projectToBoundary(embedding.toSubSpace(point));

        // back to initial dimension
        return (bp.getProjected() == null) ? null : embedding.toSpace(bp.getProjected());

    }

}
