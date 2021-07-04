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

import java.util.List;

import org.apache.commons.math3.geometry.euclidean.threed.Vector3D;
import org.apache.commons.math3.geometry.spherical.oned.Arc;
import org.apache.commons.math3.util.FastMath;
import org.apache.commons.math3.util.MathUtils;

/** Spherical polygons boundary edge.
 * @see SphericalPolygonsSet#getBoundaryLoops()
 * @see Vertex
 * @since 3.3
 */
public class Edge {

    /** Start vertex. */
    private final Vertex start;

    /** End vertex. */
    private Vertex end;

    /** Length of the arc. */
    private final double length;

    /** Circle supporting the edge. */
    private final Circle circle;

    /** Build an edge not contained in any node yet.
     * @param start start vertex
     * @param end end vertex
     * @param length length of the arc (it can be greater than \( \pi \))
     * @param circle circle supporting the edge
     */
    Edge(final Vertex start, final Vertex end, final double length, final Circle circle) {

        this.start  = start;
        this.end    = end;
        this.length = length;
        this.circle = circle;

        // connect the vertices back to the edge
        start.setOutgoing(this);
        end.setIncoming(this);

    }

    /** Get start vertex.
     * @return start vertex
     */
    public Vertex getStart() {
        return start;
    }

    /** Get end vertex.
     * @return end vertex
     */
    public Vertex getEnd() {
        return end;
    }

    /** Get the length of the arc.
     * @return length of the arc (can be greater than \( \pi \))
     */
    public double getLength() {
        return length;
    }

    /** Get the circle supporting this edge.
     * @return circle supporting this edge
     */
    public Circle getCircle() {
        return circle;
    }

    /** Get an intermediate point.
     * <p>
     * The angle along the edge should normally be between 0 and {@link #getLength()}
     * in order to remain within edge limits. However, there are no checks on the
     * value of the angle, so user can rebuild the full circle on which an edge is
     * defined if they want.
     * </p>
     * @param alpha angle along the edge, counted from {@link #getStart()}
     * @return an intermediate point
     */
    public Vector3D getPointAt(final double alpha) {
        return circle.getPointAt(alpha + circle.getPhase(start.getLocation().getVector()));
    }

    /** Connect the instance with a following edge.
     * @param next edge following the instance
     */
    void setNextEdge(final Edge next) {
        end = next.getStart();
        end.setIncoming(this);
        end.bindWith(getCircle());
    }

    /** Split the edge.
     * <p>
     * Once split, this edge is not referenced anymore by the vertices,
     * it is replaced by the two or three sub-edges and intermediate splitting
     * vertices are introduced to connect these sub-edges together.
     * </p>
     * @param splitCircle circle splitting the edge in several parts
     * @param outsideList list where to put parts that are outside of the split circle
     * @param insideList list where to put parts that are inside the split circle
     */
    void split(final Circle splitCircle,
                       final List<Edge> outsideList, final List<Edge> insideList) {

        // get the inside arc, synchronizing its phase with the edge itself
        final double edgeStart        = circle.getPhase(start.getLocation().getVector());
        final Arc    arc              = circle.getInsideArc(splitCircle);
        final double arcRelativeStart = MathUtils.normalizeAngle(arc.getInf(), edgeStart + FastMath.PI) - edgeStart;
        final double arcRelativeEnd   = arcRelativeStart + arc.getSize();
        final double unwrappedEnd     = arcRelativeEnd - MathUtils.TWO_PI;

        // build the sub-edges
        final double tolerance = circle.getTolerance();
        Vertex previousVertex = start;
        if (unwrappedEnd >= length - tolerance) {

            // the edge is entirely contained inside the circle
            // we don't split anything
            insideList.add(this);

        } else {

            // there are at least some parts of the edge that should be outside
            // (even is they are later be filtered out as being too small)
            double alreadyManagedLength = 0;
            if (unwrappedEnd >= 0) {
                // the start of the edge is inside the circle
                previousVertex = addSubEdge(previousVertex,
                                            new Vertex(new S2Point(circle.getPointAt(edgeStart + unwrappedEnd))),
                                            unwrappedEnd, insideList, splitCircle);
                alreadyManagedLength = unwrappedEnd;
            }

            if (arcRelativeStart >= length - tolerance) {
                // the edge ends while still outside of the circle
                if (unwrappedEnd >= 0) {
                    previousVertex = addSubEdge(previousVertex, end,
                                                length - alreadyManagedLength, outsideList, splitCircle);
                } else {
                    // the edge is entirely outside of the circle
                    // we don't split anything
                    outsideList.add(this);
                }
            } else {
                // the edge is long enough to enter inside the circle
                previousVertex = addSubEdge(previousVertex,
                                            new Vertex(new S2Point(circle.getPointAt(edgeStart + arcRelativeStart))),
                                            arcRelativeStart - alreadyManagedLength, outsideList, splitCircle);
                alreadyManagedLength = arcRelativeStart;

                if (arcRelativeEnd >= length - tolerance) {
                    // the edge ends while still inside of the circle
                    previousVertex = addSubEdge(previousVertex, end,
                                                length - alreadyManagedLength, insideList, splitCircle);
                } else {
                    // the edge is long enough to exit outside of the circle
                    previousVertex = addSubEdge(previousVertex,
                                                new Vertex(new S2Point(circle.getPointAt(edgeStart + arcRelativeStart))),
                                                arcRelativeStart - alreadyManagedLength, insideList, splitCircle);
                    alreadyManagedLength = arcRelativeStart;
                    previousVertex = addSubEdge(previousVertex, end,
                                                length - alreadyManagedLength, outsideList, splitCircle);
                }
            }

        }

    }

    /** Add a sub-edge to a list if long enough.
     * <p>
     * If the length of the sub-edge to add is smaller than the {@link Circle#getTolerance()}
     * tolerance of the support circle, it will be ignored.
     * </p>
     * @param subStart start of the sub-edge
     * @param subEnd end of the sub-edge
     * @param subLength length of the sub-edge
     * @param splitCircle circle splitting the edge in several parts
     * @param list list where to put the sub-edge
     * @return end vertex of the edge ({@code subEnd} if the edge was long enough and really
     * added, {@code subStart} if the edge was too small and therefore ignored)
     */
    private Vertex addSubEdge(final Vertex subStart, final Vertex subEnd, final double subLength,
                              final List<Edge> list, final Circle splitCircle) {

        if (subLength <= circle.getTolerance()) {
            // the edge is too short, we ignore it
            return subStart;
        }

        // really add the edge
        subEnd.bindWith(splitCircle);
        final Edge edge = new Edge(subStart, subEnd, subLength, circle);
        list.add(edge);
        return subEnd;

    }

}
