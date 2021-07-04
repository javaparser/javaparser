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
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;

import org.apache.commons.math3.exception.MathIllegalStateException;
import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.geometry.euclidean.threed.Vector3D;
import org.apache.commons.math3.geometry.partitioning.BSPTree;
import org.apache.commons.math3.geometry.partitioning.BSPTreeVisitor;
import org.apache.commons.math3.geometry.partitioning.BoundaryAttribute;
import org.apache.commons.math3.geometry.spherical.oned.Arc;
import org.apache.commons.math3.geometry.spherical.oned.ArcsSet;
import org.apache.commons.math3.geometry.spherical.oned.S1Point;

/** Visitor building edges.
 * @since 3.3
 */
class EdgesBuilder implements BSPTreeVisitor<Sphere2D> {

    /** Root of the tree. */
    private final BSPTree<Sphere2D> root;

    /** Tolerance below which points are consider to be identical. */
    private final double tolerance;

    /** Built edges and their associated nodes. */
    private final Map<Edge, BSPTree<Sphere2D>> edgeToNode;

    /** Reversed map. */
    private final Map<BSPTree<Sphere2D>, List<Edge>> nodeToEdgesList;

    /** Simple constructor.
     * @param root tree root
     * @param tolerance below which points are consider to be identical
     */
    EdgesBuilder(final BSPTree<Sphere2D> root, final double tolerance) {
        this.root            = root;
        this.tolerance       = tolerance;
        this.edgeToNode      = new IdentityHashMap<Edge, BSPTree<Sphere2D>>();
        this.nodeToEdgesList = new IdentityHashMap<BSPTree<Sphere2D>, List<Edge>>();
    }

    /** {@inheritDoc} */
    public Order visitOrder(final BSPTree<Sphere2D> node) {
        return Order.MINUS_SUB_PLUS;
    }

    /** {@inheritDoc} */
    public void visitInternalNode(final BSPTree<Sphere2D> node) {
        nodeToEdgesList.put(node, new ArrayList<Edge>());
        @SuppressWarnings("unchecked")
        final BoundaryAttribute<Sphere2D> attribute = (BoundaryAttribute<Sphere2D>) node.getAttribute();
        if (attribute.getPlusOutside() != null) {
            addContribution((SubCircle) attribute.getPlusOutside(), false, node);
        }
        if (attribute.getPlusInside() != null) {
            addContribution((SubCircle) attribute.getPlusInside(), true, node);
        }
    }

    /** {@inheritDoc} */
    public void visitLeafNode(final BSPTree<Sphere2D> node) {
    }

    /** Add the contribution of a boundary edge.
     * @param sub boundary facet
     * @param reversed if true, the facet has the inside on its plus side
     * @param node node to which the edge belongs
     */
    private void addContribution(final SubCircle sub, final boolean reversed,
                                 final BSPTree<Sphere2D> node) {
        final Circle circle  = (Circle) sub.getHyperplane();
        final List<Arc> arcs = ((ArcsSet) sub.getRemainingRegion()).asList();
        for (final Arc a : arcs) {
            final Vertex start = new Vertex((S2Point) circle.toSpace(new S1Point(a.getInf())));
            final Vertex end   = new Vertex((S2Point) circle.toSpace(new S1Point(a.getSup())));
            start.bindWith(circle);
            end.bindWith(circle);
            final Edge edge;
            if (reversed) {
                edge = new Edge(end, start, a.getSize(), circle.getReverse());
            } else {
                edge = new Edge(start, end, a.getSize(), circle);
            }
            edgeToNode.put(edge, node);
            nodeToEdgesList.get(node).add(edge);
        }
    }

    /** Get the edge that should naturally follow another one.
     * @param previous edge to be continued
     * @return other edge, starting where the previous one ends (they
     * have not been connected yet)
     * @exception MathIllegalStateException if there is not a single other edge
     */
    private Edge getFollowingEdge(final Edge previous)
        throws MathIllegalStateException {

        // get the candidate nodes
        final S2Point point = previous.getEnd().getLocation();
        final List<BSPTree<Sphere2D>> candidates = root.getCloseCuts(point, tolerance);

        // the following edge we are looking for must start from one of the candidates nodes
        double closest = tolerance;
        Edge following = null;
        for (final BSPTree<Sphere2D> node : candidates) {
            for (final Edge edge : nodeToEdgesList.get(node)) {
                if (edge != previous && edge.getStart().getIncoming() == null) {
                    final Vector3D edgeStart = edge.getStart().getLocation().getVector();
                    final double gap         = Vector3D.angle(point.getVector(), edgeStart);
                    if (gap <= closest) {
                        closest   = gap;
                        following = edge;
                    }
                }
            }
        }

        if (following == null) {
            final Vector3D previousStart = previous.getStart().getLocation().getVector();
            if (Vector3D.angle(point.getVector(), previousStart) <= tolerance) {
                // the edge connects back to itself
                return previous;
            }

            // this should never happen
            throw new MathIllegalStateException(LocalizedFormats.OUTLINE_BOUNDARY_LOOP_OPEN);

        }

        return following;

    }

    /** Get the boundary edges.
     * @return boundary edges
     * @exception MathIllegalStateException if there is not a single other edge
     */
    public List<Edge> getEdges() throws MathIllegalStateException {

        // connect the edges
        for (final Edge previous : edgeToNode.keySet()) {
            previous.setNextEdge(getFollowingEdge(previous));
        }

        return new ArrayList<Edge>(edgeToNode.keySet());

    }

}
