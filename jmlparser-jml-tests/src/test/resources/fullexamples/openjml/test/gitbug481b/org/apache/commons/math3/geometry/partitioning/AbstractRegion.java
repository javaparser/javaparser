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
import java.util.Collection;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.TreeSet;

import org.apache.commons.math3.geometry.Point;
import org.apache.commons.math3.geometry.Space;
import org.apache.commons.math3.geometry.Vector;

/** Abstract class for all regions, independently of geometry type or dimension.

 * @param <S> Type of the space.
 * @param <T> Type of the sub-space.

 * @since 3.0
 */
public abstract class AbstractRegion<S extends Space, T extends Space> implements Region<S> {

    /** Inside/Outside BSP tree. */
    private BSPTree<S> tree;

    /** Tolerance below which points are considered to belong to hyperplanes. */
    private final double tolerance;

    /** Size of the instance. */
    private double size;

    /** Barycenter. */
    private Point<S> barycenter;

    /** Build a region representing the whole space.
     * @param tolerance tolerance below which points are considered identical.
     */
    protected AbstractRegion(final double tolerance) {
        this.tree      = new BSPTree<S>(Boolean.TRUE);
        this.tolerance = tolerance;
    }

    /** Build a region from an inside/outside BSP tree.
     * <p>The leaf nodes of the BSP tree <em>must</em> have a
     * {@code Boolean} attribute representing the inside status of
     * the corresponding cell (true for inside cells, false for outside
     * cells). In order to avoid building too many small objects, it is
     * recommended to use the predefined constants
     * {@code Boolean.TRUE} and {@code Boolean.FALSE}. The
     * tree also <em>must</em> have either null internal nodes or
     * internal nodes representing the boundary as specified in the
     * {@link #getTree getTree} method).</p>
     * @param tree inside/outside BSP tree representing the region
     * @param tolerance tolerance below which points are considered identical.
     */
    protected AbstractRegion(final BSPTree<S> tree, final double tolerance) {
        this.tree      = tree;
        this.tolerance = tolerance;
    }

    /** Build a Region from a Boundary REPresentation (B-rep).
     * <p>The boundary is provided as a collection of {@link
     * SubHyperplane sub-hyperplanes}. Each sub-hyperplane has the
     * interior part of the region on its minus side and the exterior on
     * its plus side.</p>
     * <p>The boundary elements can be in any order, and can form
     * several non-connected sets (like for example polygons with holes
     * or a set of disjoints polyhedrons considered as a whole). In
     * fact, the elements do not even need to be connected together
     * (their topological connections are not used here). However, if the
     * boundary does not really separate an inside open from an outside
     * open (open having here its topological meaning), then subsequent
     * calls to the {@link #checkPoint(Point) checkPoint} method will not be
     * meaningful anymore.</p>
     * <p>If the boundary is empty, the region will represent the whole
     * space.</p>
     * @param boundary collection of boundary elements, as a
     * collection of {@link SubHyperplane SubHyperplane} objects
     * @param tolerance tolerance below which points are considered identical.
     */
    protected AbstractRegion(final Collection<SubHyperplane<S>> boundary, final double tolerance) {

        this.tolerance = tolerance;

        if (boundary.size() == 0) {

            // the tree represents the whole space
            tree = new BSPTree<S>(Boolean.TRUE);

        } else {

            // sort the boundary elements in decreasing size order
            // (we don't want equal size elements to be removed, so
            // we use a trick to fool the TreeSet)
            final TreeSet<SubHyperplane<S>> ordered = new TreeSet<SubHyperplane<S>>(new Comparator<SubHyperplane<S>>() {
                /** {@inheritDoc} */
                public int compare(final SubHyperplane<S> o1, final SubHyperplane<S> o2) {
                    final double size1 = o1.getSize();
                    final double size2 = o2.getSize();
                    return (size2 < size1) ? -1 : ((o1 == o2) ? 0 : +1);
                }
            });
            ordered.addAll(boundary);

            // build the tree top-down
            tree = new BSPTree<S>();
            insertCuts(tree, ordered);

            // set up the inside/outside flags
            tree.visit(new BSPTreeVisitor<S>() {

                /** {@inheritDoc} */
                public Order visitOrder(final BSPTree<S> node) {
                    return Order.PLUS_SUB_MINUS;
                }

                /** {@inheritDoc} */
                public void visitInternalNode(final BSPTree<S> node) {
                }

                /** {@inheritDoc} */
                public void visitLeafNode(final BSPTree<S> node) {
                    if (node.getParent() == null || node == node.getParent().getMinus()) {
                        node.setAttribute(Boolean.TRUE);
                    } else {
                        node.setAttribute(Boolean.FALSE);
                    }
                }
            });

        }

    }

    /** Build a convex region from an array of bounding hyperplanes.
     * @param hyperplanes array of bounding hyperplanes (if null, an
     * empty region will be built)
     * @param tolerance tolerance below which points are considered identical.
     */
    public AbstractRegion(final Hyperplane<S>[] hyperplanes, final double tolerance) {
        this.tolerance = tolerance;
        if ((hyperplanes == null) || (hyperplanes.length == 0)) {
            tree = new BSPTree<S>(Boolean.FALSE);
        } else {

            // use the first hyperplane to build the right class
            tree = hyperplanes[0].wholeSpace().getTree(false);

            // chop off parts of the space
            BSPTree<S> node = tree;
            node.setAttribute(Boolean.TRUE);
            for (final Hyperplane<S> hyperplane : hyperplanes) {
                if (node.insertCut(hyperplane)) {
                    node.setAttribute(null);
                    node.getPlus().setAttribute(Boolean.FALSE);
                    node = node.getMinus();
                    node.setAttribute(Boolean.TRUE);
                }
            }

        }

    }

    /** {@inheritDoc} */
    public abstract AbstractRegion<S, T> buildNew(BSPTree<S> newTree);

    /** Get the tolerance below which points are considered to belong to hyperplanes.
     * @return tolerance below which points are considered to belong to hyperplanes
     */
    public double getTolerance() {
        return tolerance;
    }

    /** Recursively build a tree by inserting cut sub-hyperplanes.
     * @param node current tree node (it is a leaf node at the beginning
     * of the call)
     * @param boundary collection of edges belonging to the cell defined
     * by the node
     */
    private void insertCuts(final BSPTree<S> node, final Collection<SubHyperplane<S>> boundary) {

        final Iterator<SubHyperplane<S>> iterator = boundary.iterator();

        // build the current level
        Hyperplane<S> inserted = null;
        while ((inserted == null) && iterator.hasNext()) {
            inserted = iterator.next().getHyperplane();
            if (!node.insertCut(inserted.copySelf())) {
                inserted = null;
            }
        }

        if (!iterator.hasNext()) {
            return;
        }

        // distribute the remaining edges in the two sub-trees
        final ArrayList<SubHyperplane<S>> plusList  = new ArrayList<SubHyperplane<S>>();
        final ArrayList<SubHyperplane<S>> minusList = new ArrayList<SubHyperplane<S>>();
        while (iterator.hasNext()) {
            final SubHyperplane<S> other = iterator.next();
            final SubHyperplane.SplitSubHyperplane<S> split = other.split(inserted);
            switch (split.getSide()) {
            case PLUS:
                plusList.add(other);
                break;
            case MINUS:
                minusList.add(other);
                break;
            case BOTH:
                plusList.add(split.getPlus());
                minusList.add(split.getMinus());
                break;
            default:
                // ignore the sub-hyperplanes belonging to the cut hyperplane
            }
        }

        // recurse through lower levels
        insertCuts(node.getPlus(),  plusList);
        insertCuts(node.getMinus(), minusList);

    }

    /** {@inheritDoc} */
    public AbstractRegion<S, T> copySelf() {
        return buildNew(tree.copySelf());
    }

    /** {@inheritDoc} */
    public boolean isEmpty() {
        return isEmpty(tree);
    }

    /** {@inheritDoc} */
    public boolean isEmpty(final BSPTree<S> node) {

        // we use a recursive function rather than the BSPTreeVisitor
        // interface because we can stop visiting the tree as soon as we
        // have found an inside cell

        if (node.getCut() == null) {
            // if we find an inside node, the region is not empty
            return !((Boolean) node.getAttribute());
        }

        // check both sides of the sub-tree
        return isEmpty(node.getMinus()) && isEmpty(node.getPlus());

    }

    /** {@inheritDoc} */
    public boolean isFull() {
        return isFull(tree);
    }

    /** {@inheritDoc} */
    public boolean isFull(final BSPTree<S> node) {

        // we use a recursive function rather than the BSPTreeVisitor
        // interface because we can stop visiting the tree as soon as we
        // have found an outside cell

        if (node.getCut() == null) {
            // if we find an outside node, the region does not cover full space
            return (Boolean) node.getAttribute();
        }

        // check both sides of the sub-tree
        return isFull(node.getMinus()) && isFull(node.getPlus());

    }

    /** {@inheritDoc} */
    public boolean contains(final Region<S> region) {
        return new RegionFactory<S>().difference(region, this).isEmpty();
    }

    /** {@inheritDoc}
     * @since 3.3
     */
    public BoundaryProjection<S> projectToBoundary(final Point<S> point) {
        final BoundaryProjector<S, T> projector = new BoundaryProjector<S, T>(point);
        getTree(true).visit(projector);
        return projector.getProjection();
    }

    /** Check a point with respect to the region.
     * @param point point to check
     * @return a code representing the point status: either {@link
     * Region.Location#INSIDE}, {@link Region.Location#OUTSIDE} or
     * {@link Region.Location#BOUNDARY}
     */
    public Location checkPoint(final Vector<S> point) {
        return checkPoint((Point<S>) point);
    }

    /** {@inheritDoc} */
    public Location checkPoint(final Point<S> point) {
        return checkPoint(tree, point);
    }

    /** Check a point with respect to the region starting at a given node.
     * @param node root node of the region
     * @param point point to check
     * @return a code representing the point status: either {@link
     * Region.Location#INSIDE INSIDE}, {@link Region.Location#OUTSIDE
     * OUTSIDE} or {@link Region.Location#BOUNDARY BOUNDARY}
     */
    protected Location checkPoint(final BSPTree<S> node, final Vector<S> point) {
        return checkPoint(node, (Point<S>) point);
    }

    /** Check a point with respect to the region starting at a given node.
     * @param node root node of the region
     * @param point point to check
     * @return a code representing the point status: either {@link
     * Region.Location#INSIDE INSIDE}, {@link Region.Location#OUTSIDE
     * OUTSIDE} or {@link Region.Location#BOUNDARY BOUNDARY}
     */
    protected Location checkPoint(final BSPTree<S> node, final Point<S> point) {
        final BSPTree<S> cell = node.getCell(point, tolerance);
        if (cell.getCut() == null) {
            // the point is in the interior of a cell, just check the attribute
            return ((Boolean) cell.getAttribute()) ? Location.INSIDE : Location.OUTSIDE;
        }

        // the point is on a cut-sub-hyperplane, is it on a boundary ?
        final Location minusCode = checkPoint(cell.getMinus(), point);
        final Location plusCode  = checkPoint(cell.getPlus(),  point);
        return (minusCode == plusCode) ? minusCode : Location.BOUNDARY;

    }

    /** {@inheritDoc} */
    public BSPTree<S> getTree(final boolean includeBoundaryAttributes) {
        if (includeBoundaryAttributes && (tree.getCut() != null) && (tree.getAttribute() == null)) {
            // compute the boundary attributes
            tree.visit(new BoundaryBuilder<S>());
        }
        return tree;
    }

    /** {@inheritDoc} */
    public double getBoundarySize() {
        final BoundarySizeVisitor<S> visitor = new BoundarySizeVisitor<S>();
        getTree(true).visit(visitor);
        return visitor.getSize();
    }

    /** {@inheritDoc} */
    public double getSize() {
        if (barycenter == null) {
            computeGeometricalProperties();
        }
        return size;
    }

    /** Set the size of the instance.
     * @param size size of the instance
     */
    protected void setSize(final double size) {
        this.size = size;
    }

    /** {@inheritDoc} */
    public Point<S> getBarycenter() {
        if (barycenter == null) {
            computeGeometricalProperties();
        }
        return barycenter;
    }

    /** Set the barycenter of the instance.
     * @param barycenter barycenter of the instance
     */
    protected void setBarycenter(final Vector<S> barycenter) {
        setBarycenter((Point<S>) barycenter);
    }

    /** Set the barycenter of the instance.
     * @param barycenter barycenter of the instance
     */
    protected void setBarycenter(final Point<S> barycenter) {
        this.barycenter = barycenter;
    }

    /** Compute some geometrical properties.
     * <p>The properties to compute are the barycenter and the size.</p>
     */
    protected abstract void computeGeometricalProperties();

    /** {@inheritDoc} */
    @Deprecated
    public Side side(final Hyperplane<S> hyperplane) {
        final InsideFinder<S> finder = new InsideFinder<S>(this);
        finder.recurseSides(tree, hyperplane.wholeHyperplane());
        return finder.plusFound() ?
              (finder.minusFound() ? Side.BOTH  : Side.PLUS) :
              (finder.minusFound() ? Side.MINUS : Side.HYPER);
    }

    /** {@inheritDoc} */
    public SubHyperplane<S> intersection(final SubHyperplane<S> sub) {
        return recurseIntersection(tree, sub);
    }

    /** Recursively compute the parts of a sub-hyperplane that are
     * contained in the region.
     * @param node current BSP tree node
     * @param sub sub-hyperplane traversing the region
     * @return filtered sub-hyperplane
     */
    private SubHyperplane<S> recurseIntersection(final BSPTree<S> node, final SubHyperplane<S> sub) {

        if (node.getCut() == null) {
            return (Boolean) node.getAttribute() ? sub.copySelf() : null;
        }

        final Hyperplane<S> hyperplane = node.getCut().getHyperplane();
        final SubHyperplane.SplitSubHyperplane<S> split = sub.split(hyperplane);
        if (split.getPlus() != null) {
            if (split.getMinus() != null) {
                // both sides
                final SubHyperplane<S> plus  = recurseIntersection(node.getPlus(),  split.getPlus());
                final SubHyperplane<S> minus = recurseIntersection(node.getMinus(), split.getMinus());
                if (plus == null) {
                    return minus;
                } else if (minus == null) {
                    return plus;
                } else {
                    return plus.reunite(minus);
                }
            } else {
                // only on plus side
                return recurseIntersection(node.getPlus(), sub);
            }
        } else if (split.getMinus() != null) {
            // only on minus side
            return recurseIntersection(node.getMinus(), sub);
        } else {
            // on hyperplane
            return recurseIntersection(node.getPlus(),
                                       recurseIntersection(node.getMinus(), sub));
        }

    }

    /** Transform a region.
     * <p>Applying a transform to a region consist in applying the
     * transform to all the hyperplanes of the underlying BSP tree and
     * of the boundary (and also to the sub-hyperplanes embedded in
     * these hyperplanes) and to the barycenter. The instance is not
     * modified, a new instance is built.</p>
     * @param transform transform to apply
     * @return a new region, resulting from the application of the
     * transform to the instance
     */
    public AbstractRegion<S, T> applyTransform(final Transform<S, T> transform) {

        // transform the tree, except for boundary attribute splitters
        final Map<BSPTree<S>, BSPTree<S>> map = new HashMap<BSPTree<S>, BSPTree<S>>();
        final BSPTree<S> transformedTree = recurseTransform(getTree(false), transform, map);

        // set up the boundary attributes splitters
        for (final Map.Entry<BSPTree<S>, BSPTree<S>> entry : map.entrySet()) {
            if (entry.getKey().getCut() != null) {
                @SuppressWarnings("unchecked")
                BoundaryAttribute<S> original = (BoundaryAttribute<S>) entry.getKey().getAttribute();
                if (original != null) {
                    @SuppressWarnings("unchecked")
                    BoundaryAttribute<S> transformed = (BoundaryAttribute<S>) entry.getValue().getAttribute();
                    for (final BSPTree<S> splitter : original.getSplitters()) {
                        transformed.getSplitters().add(map.get(splitter));
                    }
                }
            }
        }

        return buildNew(transformedTree);

    }

    /** Recursively transform an inside/outside BSP-tree.
     * @param node current BSP tree node
     * @param transform transform to apply
     * @param map transformed nodes map
     * @return a new tree
     */
    @SuppressWarnings("unchecked")
    private BSPTree<S> recurseTransform(final BSPTree<S> node, final Transform<S, T> transform,
                                        final Map<BSPTree<S>, BSPTree<S>> map) {

        final BSPTree<S> transformedNode;
        if (node.getCut() == null) {
            transformedNode = new BSPTree<S>(node.getAttribute());
        } else {

            final SubHyperplane<S>  sub = node.getCut();
            final SubHyperplane<S> tSub = ((AbstractSubHyperplane<S, T>) sub).applyTransform(transform);
            BoundaryAttribute<S> attribute = (BoundaryAttribute<S>) node.getAttribute();
            if (attribute != null) {
                final SubHyperplane<S> tPO = (attribute.getPlusOutside() == null) ?
                    null : ((AbstractSubHyperplane<S, T>) attribute.getPlusOutside()).applyTransform(transform);
                final SubHyperplane<S> tPI = (attribute.getPlusInside()  == null) ?
                    null  : ((AbstractSubHyperplane<S, T>) attribute.getPlusInside()).applyTransform(transform);
                // we start with an empty list of splitters, it will be filled in out of recursion
                attribute = new BoundaryAttribute<S>(tPO, tPI, new NodesSet<S>());
            }

            transformedNode = new BSPTree<S>(tSub,
                                             recurseTransform(node.getPlus(),  transform, map),
                                             recurseTransform(node.getMinus(), transform, map),
                                             attribute);
        }

        map.put(node, transformedNode);
        return transformedNode;

    }

}
