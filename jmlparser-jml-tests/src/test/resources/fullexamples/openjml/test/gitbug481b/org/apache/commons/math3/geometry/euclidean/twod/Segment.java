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

import org.apache.commons.math3.geometry.Point;
import org.apache.commons.math3.util.FastMath;

/** Simple container for a two-points segment.
 * @since 3.0
 */
public class Segment {

    /** Start point of the segment. */
    private final Vector2D start;

    /** End point of the segment. */
    private final Vector2D end;

    /** Line containing the segment. */
    private final Line     line;

    /** Build a segment.
     * @param start start point of the segment
     * @param end end point of the segment
     * @param line line containing the segment
     */
    public Segment(final Vector2D start, final Vector2D end, final Line line) {
        this.start  = start;
        this.end    = end;
        this.line   = line;
    }

    /** Get the start point of the segment.
     * @return start point of the segment
     */
    public Vector2D getStart() {
        return start;
    }

    /** Get the end point of the segment.
     * @return end point of the segment
     */
    public Vector2D getEnd() {
        return end;
    }

    /** Get the line containing the segment.
     * @return line containing the segment
     */
    public Line getLine() {
        return line;
    }

    /** Calculates the shortest distance from a point to this line segment.
     * <p>
     * If the perpendicular extension from the point to the line does not
     * cross in the bounds of the line segment, the shortest distance to
     * the two end points will be returned.
     * </p>
     *
     * Algorithm adapted from:
     * <a href="http://www.codeguru.com/forum/printthread.php?s=cc8cf0596231f9a7dba4da6e77c29db3&t=194400&pp=15&page=1">
     * Thread @ Codeguru</a>
     *
     * @param p to check
     * @return distance between the instance and the point
     * @since 3.1
     */
    public double distance(final Vector2D p) {
        final double deltaX = end.getX() - start.getX();
        final double deltaY = end.getY() - start.getY();

        final double r = ((p.getX() - start.getX()) * deltaX + (p.getY() - start.getY()) * deltaY) /
                         (deltaX * deltaX + deltaY * deltaY);

        // r == 0 => P = startPt
        // r == 1 => P = endPt
        // r < 0 => P is on the backward extension of the segment
        // r > 1 => P is on the forward extension of the segment
        // 0 < r < 1 => P is on the segment

        // if point isn't on the line segment, just return the shortest distance to the end points
        if (r < 0 || r > 1) {
            final double dist1 = getStart().distance((Point<Euclidean2D>) p);
            final double dist2 = getEnd().distance((Point<Euclidean2D>) p);

            return FastMath.min(dist1, dist2);
        }
        else {
            // find point on line and see if it is in the line segment
            final double px = start.getX() + r * deltaX;
            final double py = start.getY() + r * deltaY;

            final Vector2D interPt = new Vector2D(px, py);
            return interPt.distance((Point<Euclidean2D>) p);
        }
    }
}
