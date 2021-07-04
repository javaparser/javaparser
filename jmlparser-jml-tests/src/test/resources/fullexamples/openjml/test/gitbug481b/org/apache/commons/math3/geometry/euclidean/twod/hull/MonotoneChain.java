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
package org.apache.commons.math3.geometry.euclidean.twod.hull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;

import org.apache.commons.math3.geometry.euclidean.twod.Line;
import org.apache.commons.math3.geometry.euclidean.twod.Vector2D;
import org.apache.commons.math3.util.FastMath;
import org.apache.commons.math3.util.Precision;

/**
 * Implements Andrew's monotone chain method to generate the convex hull of a finite set of
 * points in the two-dimensional euclidean space.
 * <p>
 * The runtime complexity is O(n log n), with n being the number of input points. If the
 * point set is already sorted (by x-coordinate), the runtime complexity is O(n).
 * <p>
 * The implementation is not sensitive to collinear points on the hull. The parameter
 * {@code includeCollinearPoints} allows to control the behavior with regard to collinear points.
 * If {@code true}, all points on the boundary of the hull will be added to the hull vertices,
 * otherwise only the extreme points will be present. By default, collinear points are not added
 * as hull vertices.
 * <p>
 * The {@code tolerance} parameter (default: 1e-10) is used as epsilon criteria to determine
 * identical and collinear points.
 *
 * @see <a href="http://en.wikibooks.org/wiki/Algorithm_Implementation/Geometry/Convex_hull/Monotone_chain">
 * Andrew's monotone chain algorithm (Wikibooks)</a>
 * @since 3.3
 */
public class MonotoneChain extends AbstractConvexHullGenerator2D {

    /**
     * Create a new MonotoneChain instance.
     */
    public MonotoneChain() {
        this(false);
    }

    /**
     * Create a new MonotoneChain instance.
     * @param includeCollinearPoints whether collinear points shall be added as hull vertices
     */
    public MonotoneChain(final boolean includeCollinearPoints) {
        super(includeCollinearPoints);
    }

    /**
     * Create a new MonotoneChain instance.
     * @param includeCollinearPoints whether collinear points shall be added as hull vertices
     * @param tolerance tolerance below which points are considered identical
     */
    public MonotoneChain(final boolean includeCollinearPoints, final double tolerance) {
        super(includeCollinearPoints, tolerance);
    }

    /** {@inheritDoc} */
    @Override
    public Collection<Vector2D> findHullVertices(final Collection<Vector2D> points) {

        final List<Vector2D> pointsSortedByXAxis = new ArrayList<Vector2D>(points);

        // sort the points in increasing order on the x-axis
        Collections.sort(pointsSortedByXAxis, new Comparator<Vector2D>() {
            /** {@inheritDoc} */
            public int compare(final Vector2D o1, final Vector2D o2) {
                final double tolerance = getTolerance();
                // need to take the tolerance value into account, otherwise collinear points
                // will not be handled correctly when building the upper/lower hull
                final int diff = Precision.compareTo(o1.getX(), o2.getX(), tolerance);
                if (diff == 0) {
                    return Precision.compareTo(o1.getY(), o2.getY(), tolerance);
                } else {
                    return diff;
                }
            }
        });

        // build lower hull
        final List<Vector2D> lowerHull = new ArrayList<Vector2D>();
        for (Vector2D p : pointsSortedByXAxis) {
            updateHull(p, lowerHull);
        }

        // build upper hull
        final List<Vector2D> upperHull = new ArrayList<Vector2D>();
        for (int idx = pointsSortedByXAxis.size() - 1; idx >= 0; idx--) {
            final Vector2D p = pointsSortedByXAxis.get(idx);
            updateHull(p, upperHull);
        }

        // concatenate the lower and upper hulls
        // the last point of each list is omitted as it is repeated at the beginning of the other list
        final List<Vector2D> hullVertices = new ArrayList<Vector2D>(lowerHull.size() + upperHull.size() - 2);
        for (int idx = 0; idx < lowerHull.size() - 1; idx++) {
            hullVertices.add(lowerHull.get(idx));
        }
        for (int idx = 0; idx < upperHull.size() - 1; idx++) {
            hullVertices.add(upperHull.get(idx));
        }

        // special case: if the lower and upper hull may contain only 1 point if all are identical
        if (hullVertices.isEmpty() && ! lowerHull.isEmpty()) {
            hullVertices.add(lowerHull.get(0));
        }

        return hullVertices;
    }

    /**
     * Update the partial hull with the current point.
     *
     * @param point the current point
     * @param hull the partial hull
     */
    private void updateHull(final Vector2D point, final List<Vector2D> hull) {
        final double tolerance = getTolerance();

        if (hull.size() == 1) {
            // ensure that we do not add an identical point
            final Vector2D p1 = hull.get(0);
            if (p1.distance(point) < tolerance) {
                return;
            }
        }

        while (hull.size() >= 2) {
            final int size = hull.size();
            final Vector2D p1 = hull.get(size - 2);
            final Vector2D p2 = hull.get(size - 1);

            final double offset = new Line(p1, p2, tolerance).getOffset(point);
            if (FastMath.abs(offset) < tolerance) {
                // the point is collinear to the line (p1, p2)

                final double distanceToCurrent = p1.distance(point);
                if (distanceToCurrent < tolerance || p2.distance(point) < tolerance) {
                    // the point is assumed to be identical to either p1 or p2
                    return;
                }

                final double distanceToLast = p1.distance(p2);
                if (isIncludeCollinearPoints()) {
                    final int index = distanceToCurrent < distanceToLast ? size - 1 : size;
                    hull.add(index, point);
                } else {
                    if (distanceToCurrent > distanceToLast) {
                        hull.remove(size - 1);
                        hull.add(point);
                    }
                }
                return;
            } else if (offset > 0) {
                hull.remove(size - 1);
            } else {
                break;
            }
        }
        hull.add(point);
    }

}
