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

import java.util.ArrayList;
import java.util.List;

/** Spherical polygons boundary vertex.
 * @see SphericalPolygonsSet#getBoundaryLoops()
 * @see Edge
 * @since 3.3
 */
public class Vertex {

    /** Vertex location. */
    private final S2Point location;

    /** Incoming edge. */
    private Edge incoming;

    /** Outgoing edge. */
    private Edge outgoing;

    /** Circles bound with this vertex. */
    private final List<Circle> circles;

    /** Build a non-processed vertex not owned by any node yet.
     * @param location vertex location
     */
    Vertex(final S2Point location) {
        this.location = location;
        this.incoming = null;
        this.outgoing = null;
        this.circles  = new ArrayList<Circle>();
    }

    /** Get Vertex location.
     * @return vertex location
     */
    public S2Point getLocation() {
        return location;
    }

    /** Bind a circle considered to contain this vertex.
     * @param circle circle to bind with this vertex
     */
    void bindWith(final Circle circle) {
        circles.add(circle);
    }

    /** Get the common circle bound with both the instance and another vertex, if any.
     * <p>
     * When two vertices are both bound to the same circle, this means they are
     * already handled by node associated with this circle, so there is no need
     * to create a cut hyperplane for them.
     * </p>
     * @param vertex other vertex to check instance against
     * @return circle bound with both the instance and another vertex, or null if the
     * two vertices do not share a circle yet
     */
    Circle sharedCircleWith(final Vertex vertex) {
        for (final Circle circle1 : circles) {
            for (final Circle circle2 : vertex.circles) {
                if (circle1 == circle2) {
                    return circle1;
                }
            }
        }
        return null;
    }

    /** Set incoming edge.
     * <p>
     * The circle supporting the incoming edge is automatically bound
     * with the instance.
     * </p>
     * @param incoming incoming edge
     */
    void setIncoming(final Edge incoming) {
        this.incoming = incoming;
        bindWith(incoming.getCircle());
    }

    /** Get incoming edge.
     * @return incoming edge
     */
    public Edge getIncoming() {
        return incoming;
    }

    /** Set outgoing edge.
     * <p>
     * The circle supporting the outgoing edge is automatically bound
     * with the instance.
     * </p>
     * @param outgoing outgoing edge
     */
    void setOutgoing(final Edge outgoing) {
        this.outgoing = outgoing;
        bindWith(outgoing.getCircle());
    }

    /** Get outgoing edge.
     * @return outgoing edge
     */
    public Edge getOutgoing() {
        return outgoing;
    }

}
