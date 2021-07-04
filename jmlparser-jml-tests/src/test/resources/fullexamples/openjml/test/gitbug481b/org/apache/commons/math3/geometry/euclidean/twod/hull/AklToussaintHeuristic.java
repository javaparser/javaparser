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
import java.util.List;

import org.apache.commons.math3.geometry.euclidean.twod.Vector2D;

/**
 * A simple heuristic to improve the performance of convex hull algorithms.
 * <p>
 * The heuristic is based on the idea of a convex quadrilateral, which is formed by
 * four points with the lowest and highest x / y coordinates. Any point that lies inside
 * this quadrilateral can not be part of the convex hull and can thus be safely discarded
 * before generating the convex hull itself.
 * <p>
 * The complexity of the operation is O(n), and may greatly improve the time it takes to
 * construct the convex hull afterwards, depending on the point distribution.
 *
 * @see <a href="http://en.wikipedia.org/wiki/Convex_hull_algorithms#Akl-Toussaint_heuristic">
 * Akl-Toussaint heuristic (Wikipedia)</a>
 * @since 3.3
 */
public final class AklToussaintHeuristic {

    /** Hide utility constructor. */
    private AklToussaintHeuristic() {
    }

    /**
     * Returns a point set that is reduced by all points for which it is safe to assume
     * that they are not part of the convex hull.
     *
     * @param points the original point set
     * @return a reduced point set, useful as input for convex hull algorithms
     */
    public static Collection<Vector2D> reducePoints(final Collection<Vector2D> points) {

        // find the leftmost point
        int size = 0;
        Vector2D minX = null;
        Vector2D maxX = null;
        Vector2D minY = null;
        Vector2D maxY = null;
        for (Vector2D p : points) {
            if (minX == null || p.getX() < minX.getX()) {
                minX = p;
            }
            if (maxX == null || p.getX() > maxX.getX()) {
                maxX = p;
            }
            if (minY == null || p.getY() < minY.getY()) {
                minY = p;
            }
            if (maxY == null || p.getY() > maxY.getY()) {
                maxY = p;
            }
            size++;
        }

        if (size < 4) {
            return points;
        }

        final List<Vector2D> quadrilateral = buildQuadrilateral(minY, maxX, maxY, minX);
        // if the quadrilateral is not well formed, e.g. only 2 points, do not attempt to reduce
        if (quadrilateral.size() < 3) {
            return points;
        }

        final List<Vector2D> reducedPoints = new ArrayList<Vector2D>(quadrilateral);
        for (final Vector2D p : points) {
            // check all points if they are within the quadrilateral
            // in which case they can not be part of the convex hull
            if (!insideQuadrilateral(p, quadrilateral)) {
                reducedPoints.add(p);
            }
        }

        return reducedPoints;
    }

    /**
     * Build the convex quadrilateral with the found corner points (with min/max x/y coordinates).
     *
     * @param points the respective points with min/max x/y coordinate
     * @return the quadrilateral
     */
    private static List<Vector2D> buildQuadrilateral(final Vector2D... points) {
        List<Vector2D> quadrilateral = new ArrayList<Vector2D>();
        for (Vector2D p : points) {
            if (!quadrilateral.contains(p)) {
                quadrilateral.add(p);
            }
        }
        return quadrilateral;
    }

    /**
     * Checks if the given point is located within the convex quadrilateral.
     * @param point the point to check
     * @param quadrilateralPoints the convex quadrilateral, represented by 4 points
     * @return {@code true} if the point is inside the quadrilateral, {@code false} otherwise
     */
    private static boolean insideQuadrilateral(final Vector2D point,
                                               final List<Vector2D> quadrilateralPoints) {

        Vector2D p1 = quadrilateralPoints.get(0);
        Vector2D p2 = quadrilateralPoints.get(1);

        if (point.equals(p1) || point.equals(p2)) {
            return true;
        }

        // get the location of the point relative to the first two vertices
        final double last = point.crossProduct(p1, p2);
        final int size = quadrilateralPoints.size();
        // loop through the rest of the vertices
        for (int i = 1; i < size; i++) {
            p1 = p2;
            p2 = quadrilateralPoints.get((i + 1) == size ? 0 : i + 1);

            if (point.equals(p1) || point.equals(p2)) {
                return true;
            }

            // do side of line test: multiply the last location with this location
            // if they are the same sign then the operation will yield a positive result
            // -x * -y = +xy, x * y = +xy, -x * y = -xy, x * -y = -xy
            if (last * point.crossProduct(p1, p2) < 0) {
                return false;
            }
        }
        return true;
    }

}
