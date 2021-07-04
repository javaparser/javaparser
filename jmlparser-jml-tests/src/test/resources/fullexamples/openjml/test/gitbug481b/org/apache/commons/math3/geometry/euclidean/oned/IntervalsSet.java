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

import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.NoSuchElementException;

import org.apache.commons.math3.geometry.Point;
import org.apache.commons.math3.geometry.partitioning.AbstractRegion;
import org.apache.commons.math3.geometry.partitioning.BSPTree;
import org.apache.commons.math3.geometry.partitioning.BoundaryProjection;
import org.apache.commons.math3.geometry.partitioning.SubHyperplane;
import org.apache.commons.math3.util.Precision;

/** This class represents a 1D region: a set of intervals.
 * @since 3.0
 */
public class IntervalsSet extends AbstractRegion<Euclidean1D, Euclidean1D> implements Iterable<double[]> {

    /** Default value for tolerance. */
    private static final double DEFAULT_TOLERANCE = 1.0e-10;

    /** Build an intervals set representing the whole real line.
     * @param tolerance tolerance below which points are considered identical.
     * @since 3.3
     */
    public IntervalsSet(final double tolerance) {
        super(tolerance);
    }

    /** Build an intervals set corresponding to a single interval.
     * @param lower lower bound of the interval, must be lesser or equal
     * to {@code upper} (may be {@code Double.NEGATIVE_INFINITY})
     * @param upper upper bound of the interval, must be greater or equal
     * to {@code lower} (may be {@code Double.POSITIVE_INFINITY})
     * @param tolerance tolerance below which points are considered identical.
     * @since 3.3
     */
    public IntervalsSet(final double lower, final double upper, final double tolerance) {
        super(buildTree(lower, upper, tolerance), tolerance);
    }

    /** Build an intervals set from an inside/outside BSP tree.
     * <p>The leaf nodes of the BSP tree <em>must</em> have a
     * {@code Boolean} attribute representing the inside status of
     * the corresponding cell (true for inside cells, false for outside
     * cells). In order to avoid building too many small objects, it is
     * recommended to use the predefined constants
     * {@code Boolean.TRUE} and {@code Boolean.FALSE}</p>
     * @param tree inside/outside BSP tree representing the intervals set
     * @param tolerance tolerance below which points are considered identical.
     * @since 3.3
     */
    public IntervalsSet(final BSPTree<Euclidean1D> tree, final double tolerance) {
        super(tree, tolerance);
    }

    /** Build an intervals set from a Boundary REPresentation (B-rep).
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
     * calls to the {@link
     * org.apache.commons.math3.geometry.partitioning.Region#checkPoint(org.apache.commons.math3.geometry.Point)
     * checkPoint} method will not be meaningful anymore.</p>
     * <p>If the boundary is empty, the region will represent the whole
     * space.</p>
     * @param boundary collection of boundary elements
     * @param tolerance tolerance below which points are considered identical.
     * @since 3.3
     */
    public IntervalsSet(final Collection<SubHyperplane<Euclidean1D>> boundary,
                        final double tolerance) {
        super(boundary, tolerance);
    }

    /** Build an intervals set representing the whole real line.
     * @deprecated as of 3.1 replaced with {@link #IntervalsSet(double)}
     */
    @Deprecated
    public IntervalsSet() {
        this(DEFAULT_TOLERANCE);
    }

    /** Build an intervals set corresponding to a single interval.
     * @param lower lower bound of the interval, must be lesser or equal
     * to {@code upper} (may be {@code Double.NEGATIVE_INFINITY})
     * @param upper upper bound of the interval, must be greater or equal
     * to {@code lower} (may be {@code Double.POSITIVE_INFINITY})
     * @deprecated as of 3.3 replaced with {@link #IntervalsSet(double, double, double)}
     */
    @Deprecated
    public IntervalsSet(final double lower, final double upper) {
        this(lower, upper, DEFAULT_TOLERANCE);
    }

    /** Build an intervals set from an inside/outside BSP tree.
     * <p>The leaf nodes of the BSP tree <em>must</em> have a
     * {@code Boolean} attribute representing the inside status of
     * the corresponding cell (true for inside cells, false for outside
     * cells). In order to avoid building too many small objects, it is
     * recommended to use the predefined constants
     * {@code Boolean.TRUE} and {@code Boolean.FALSE}</p>
     * @param tree inside/outside BSP tree representing the intervals set
     * @deprecated as of 3.3, replaced with {@link #IntervalsSet(BSPTree, double)}
     */
    @Deprecated
    public IntervalsSet(final BSPTree<Euclidean1D> tree) {
        this(tree, DEFAULT_TOLERANCE);
    }

    /** Build an intervals set from a Boundary REPresentation (B-rep).
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
     * calls to the {@link
     * org.apache.commons.math3.geometry.partitioning.Region#checkPoint(org.apache.commons.math3.geometry.Point)
     * checkPoint} method will not be meaningful anymore.</p>
     * <p>If the boundary is empty, the region will represent the whole
     * space.</p>
     * @param boundary collection of boundary elements
     * @deprecated as of 3.3, replaced with {@link #IntervalsSet(Collection, double)}
     */
    @Deprecated
    public IntervalsSet(final Collection<SubHyperplane<Euclidean1D>> boundary) {
        this(boundary, DEFAULT_TOLERANCE);
    }

    /** Build an inside/outside tree representing a single interval.
     * @param lower lower bound of the interval, must be lesser or equal
     * to {@code upper} (may be {@code Double.NEGATIVE_INFINITY})
     * @param upper upper bound of the interval, must be greater or equal
     * to {@code lower} (may be {@code Double.POSITIVE_INFINITY})
     * @param tolerance tolerance below which points are considered identical.
     * @return the built tree
     */
    private static BSPTree<Euclidean1D> buildTree(final double lower, final double upper,
                                                  final double tolerance) {
        if (Double.isInfinite(lower) && (lower < 0)) {
            if (Double.isInfinite(upper) && (upper > 0)) {
                // the tree must cover the whole real line
                return new BSPTree<Euclidean1D>(Boolean.TRUE);
            }
            // the tree must be open on the negative infinity side
            final SubHyperplane<Euclidean1D> upperCut =
                new OrientedPoint(new Vector1D(upper), true, tolerance).wholeHyperplane();
            return new BSPTree<Euclidean1D>(upperCut,
                               new BSPTree<Euclidean1D>(Boolean.FALSE),
                               new BSPTree<Euclidean1D>(Boolean.TRUE),
                               null);
        }
        final SubHyperplane<Euclidean1D> lowerCut =
            new OrientedPoint(new Vector1D(lower), false, tolerance).wholeHyperplane();
        if (Double.isInfinite(upper) && (upper > 0)) {
            // the tree must be open on the positive infinity side
            return new BSPTree<Euclidean1D>(lowerCut,
                                            new BSPTree<Euclidean1D>(Boolean.FALSE),
                                            new BSPTree<Euclidean1D>(Boolean.TRUE),
                                            null);
        }

        // the tree must be bounded on the two sides
        final SubHyperplane<Euclidean1D> upperCut =
            new OrientedPoint(new Vector1D(upper), true, tolerance).wholeHyperplane();
        return new BSPTree<Euclidean1D>(lowerCut,
                                        new BSPTree<Euclidean1D>(Boolean.FALSE),
                                        new BSPTree<Euclidean1D>(upperCut,
                                                                 new BSPTree<Euclidean1D>(Boolean.FALSE),
                                                                 new BSPTree<Euclidean1D>(Boolean.TRUE),
                                                                 null),
                                        null);

    }

    /** {@inheritDoc} */
    @Override
    public IntervalsSet buildNew(final BSPTree<Euclidean1D> tree) {
        return new IntervalsSet(tree, getTolerance());
    }

    /** {@inheritDoc} */
    @Override
    protected void computeGeometricalProperties() {
        if (getTree(false).getCut() == null) {
            setBarycenter((Point<Euclidean1D>) Vector1D.NaN);
            setSize(((Boolean) getTree(false).getAttribute()) ? Double.POSITIVE_INFINITY : 0);
        } else {
            double size = 0.0;
            double sum = 0.0;
            for (final Interval interval : asList()) {
                size += interval.getSize();
                sum  += interval.getSize() * interval.getBarycenter();
            }
            setSize(size);
            if (Double.isInfinite(size)) {
                setBarycenter((Point<Euclidean1D>) Vector1D.NaN);
            } else if (size >= Precision.SAFE_MIN) {
                setBarycenter((Point<Euclidean1D>) new Vector1D(sum / size));
            } else {
                setBarycenter((Point<Euclidean1D>) ((OrientedPoint) getTree(false).getCut().getHyperplane()).getLocation());
            }
        }
    }

    /** Get the lowest value belonging to the instance.
     * @return lowest value belonging to the instance
     * ({@code Double.NEGATIVE_INFINITY} if the instance doesn't
     * have any low bound, {@code Double.POSITIVE_INFINITY} if the
     * instance is empty)
     */
    public double getInf() {
        BSPTree<Euclidean1D> node = getTree(false);
        double  inf  = Double.POSITIVE_INFINITY;
        while (node.getCut() != null) {
            final OrientedPoint op = (OrientedPoint) node.getCut().getHyperplane();
            inf  = op.getLocation().getX();
            node = op.isDirect() ? node.getMinus() : node.getPlus();
        }
        return ((Boolean) node.getAttribute()) ? Double.NEGATIVE_INFINITY : inf;
    }

    /** Get the highest value belonging to the instance.
     * @return highest value belonging to the instance
     * ({@code Double.POSITIVE_INFINITY} if the instance doesn't
     * have any high bound, {@code Double.NEGATIVE_INFINITY} if the
     * instance is empty)
     */
    public double getSup() {
        BSPTree<Euclidean1D> node = getTree(false);
        double  sup  = Double.NEGATIVE_INFINITY;
        while (node.getCut() != null) {
            final OrientedPoint op = (OrientedPoint) node.getCut().getHyperplane();
            sup  = op.getLocation().getX();
            node = op.isDirect() ? node.getPlus() : node.getMinus();
        }
        return ((Boolean) node.getAttribute()) ? Double.POSITIVE_INFINITY : sup;
    }

    /** {@inheritDoc}
     * @since 3.3
     */
    @Override
    public BoundaryProjection<Euclidean1D> projectToBoundary(final Point<Euclidean1D> point) {

        // get position of test point
        final double x = ((Vector1D) point).getX();

        double previous = Double.NEGATIVE_INFINITY;
        for (final double[] a : this) {
            if (x < a[0]) {
                // the test point lies between the previous and the current intervals
                // offset will be positive
                final double previousOffset = x - previous;
                final double currentOffset  = a[0] - x;
                if (previousOffset < currentOffset) {
                    return new BoundaryProjection<Euclidean1D>(point, finiteOrNullPoint(previous), previousOffset);
                } else {
                    return new BoundaryProjection<Euclidean1D>(point, finiteOrNullPoint(a[0]), currentOffset);
                }
            } else if (x <= a[1]) {
                // the test point lies within the current interval
                // offset will be negative
                final double offset0 = a[0] - x;
                final double offset1 = x - a[1];
                if (offset0 < offset1) {
                    return new BoundaryProjection<Euclidean1D>(point, finiteOrNullPoint(a[1]), offset1);
                } else {
                    return new BoundaryProjection<Euclidean1D>(point, finiteOrNullPoint(a[0]), offset0);
                }
            }
            previous = a[1];
        }

        // the test point if past the last sub-interval
        return new BoundaryProjection<Euclidean1D>(point, finiteOrNullPoint(previous), x - previous);

    }

    /** Build a finite point.
     * @param x abscissa of the point
     * @return a new point for finite abscissa, null otherwise
     */
    private Vector1D finiteOrNullPoint(final double x) {
        return Double.isInfinite(x) ? null : new Vector1D(x);
    }

    /** Build an ordered list of intervals representing the instance.
     * <p>This method builds this intervals set as an ordered list of
     * {@link Interval Interval} elements. If the intervals set has no
     * lower limit, the first interval will have its low bound equal to
     * {@code Double.NEGATIVE_INFINITY}. If the intervals set has
     * no upper limit, the last interval will have its upper bound equal
     * to {@code Double.POSITIVE_INFINITY}. An empty tree will
     * build an empty list while a tree representing the whole real line
     * will build a one element list with both bounds being
     * infinite.</p>
     * @return a new ordered list containing {@link Interval Interval}
     * elements
     */
    public List<Interval> asList() {
        final List<Interval> list = new ArrayList<Interval>();
        for (final double[] a : this) {
            list.add(new Interval(a[0], a[1]));
        }
        return list;
    }

    /** Get the first leaf node of a tree.
     * @param root tree root
     * @return first leaf node
     */
    private BSPTree<Euclidean1D> getFirstLeaf(final BSPTree<Euclidean1D> root) {

        if (root.getCut() == null) {
            return root;
        }

        // find the smallest internal node
        BSPTree<Euclidean1D> smallest = null;
        for (BSPTree<Euclidean1D> n = root; n != null; n = previousInternalNode(n)) {
            smallest = n;
        }

        return leafBefore(smallest);

    }

    /** Get the node corresponding to the first interval boundary.
     * @return smallest internal node,
     * or null if there are no internal nodes (i.e. the set is either empty or covers the real line)
     */
    private BSPTree<Euclidean1D> getFirstIntervalBoundary() {

        // start search at the tree root
        BSPTree<Euclidean1D> node = getTree(false);
        if (node.getCut() == null) {
            return null;
        }

        // walk tree until we find the smallest internal node
        node = getFirstLeaf(node).getParent();

        // walk tree until we find an interval boundary
        while (node != null && !(isIntervalStart(node) || isIntervalEnd(node))) {
            node = nextInternalNode(node);
        }

        return node;

    }

    /** Check if an internal node corresponds to the start abscissa of an interval.
     * @param node internal node to check
     * @return true if the node corresponds to the start abscissa of an interval
     */
    private boolean isIntervalStart(final BSPTree<Euclidean1D> node) {

        if ((Boolean) leafBefore(node).getAttribute()) {
            // it has an inside cell before it, it may end an interval but not start it
            return false;
        }

        if (!(Boolean) leafAfter(node).getAttribute()) {
            // it has an outside cell after it, it is a dummy cut away from real intervals
            return false;
        }

        // the cell has an outside before and an inside after it
        // it is the start of an interval
        return true;

    }

    /** Check if an internal node corresponds to the end abscissa of an interval.
     * @param node internal node to check
     * @return true if the node corresponds to the end abscissa of an interval
     */
    private boolean isIntervalEnd(final BSPTree<Euclidean1D> node) {

        if (!(Boolean) leafBefore(node).getAttribute()) {
            // it has an outside cell before it, it may start an interval but not end it
            return false;
        }

        if ((Boolean) leafAfter(node).getAttribute()) {
            // it has an inside cell after it, it is a dummy cut in the middle of an interval
            return false;
        }

        // the cell has an inside before and an outside after it
        // it is the end of an interval
        return true;

    }

    /** Get the next internal node.
     * @param node current internal node
     * @return next internal node in ascending order, or null
     * if this is the last internal node
     */
    private BSPTree<Euclidean1D> nextInternalNode(BSPTree<Euclidean1D> node) {

        if (childAfter(node).getCut() != null) {
            // the next node is in the sub-tree
            return leafAfter(node).getParent();
        }

        // there is nothing left deeper in the tree, we backtrack
        while (isAfterParent(node)) {
            node = node.getParent();
        }
        return node.getParent();

    }

    /** Get the previous internal node.
     * @param node current internal node
     * @return previous internal node in ascending order, or null
     * if this is the first internal node
     */
    private BSPTree<Euclidean1D> previousInternalNode(BSPTree<Euclidean1D> node) {

        if (childBefore(node).getCut() != null) {
            // the next node is in the sub-tree
            return leafBefore(node).getParent();
        }

        // there is nothing left deeper in the tree, we backtrack
        while (isBeforeParent(node)) {
            node = node.getParent();
        }
        return node.getParent();

    }

    /** Find the leaf node just before an internal node.
     * @param node internal node at which the sub-tree starts
     * @return leaf node just before the internal node
     */
    private BSPTree<Euclidean1D> leafBefore(BSPTree<Euclidean1D> node) {

        node = childBefore(node);
        while (node.getCut() != null) {
            node = childAfter(node);
        }

        return node;

    }

    /** Find the leaf node just after an internal node.
     * @param node internal node at which the sub-tree starts
     * @return leaf node just after the internal node
     */
    private BSPTree<Euclidean1D> leafAfter(BSPTree<Euclidean1D> node) {

        node = childAfter(node);
        while (node.getCut() != null) {
            node = childBefore(node);
        }

        return node;

    }

    /** Check if a node is the child before its parent in ascending order.
     * @param node child node considered
     * @return true is the node has a parent end is before it in ascending order
     */
    private boolean isBeforeParent(final BSPTree<Euclidean1D> node) {
        final BSPTree<Euclidean1D> parent = node.getParent();
        if (parent == null) {
            return false;
        } else {
            return node == childBefore(parent);
        }
    }

    /** Check if a node is the child after its parent in ascending order.
     * @param node child node considered
     * @return true is the node has a parent end is after it in ascending order
     */
    private boolean isAfterParent(final BSPTree<Euclidean1D> node) {
        final BSPTree<Euclidean1D> parent = node.getParent();
        if (parent == null) {
            return false;
        } else {
            return node == childAfter(parent);
        }
    }

    /** Find the child node just before an internal node.
     * @param node internal node at which the sub-tree starts
     * @return child node just before the internal node
     */
    private BSPTree<Euclidean1D> childBefore(BSPTree<Euclidean1D> node) {
        if (isDirect(node)) {
            // smaller abscissas are on minus side, larger abscissas are on plus side
            return node.getMinus();
        } else {
            // smaller abscissas are on plus side, larger abscissas are on minus side
            return node.getPlus();
        }
    }

    /** Find the child node just after an internal node.
     * @param node internal node at which the sub-tree starts
     * @return child node just after the internal node
     */
    private BSPTree<Euclidean1D> childAfter(BSPTree<Euclidean1D> node) {
        if (isDirect(node)) {
            // smaller abscissas are on minus side, larger abscissas are on plus side
            return node.getPlus();
        } else {
            // smaller abscissas are on plus side, larger abscissas are on minus side
            return node.getMinus();
        }
    }

    /** Check if an internal node has a direct oriented point.
     * @param node internal node to check
     * @return true if the oriented point is direct
     */
    private boolean isDirect(final BSPTree<Euclidean1D> node) {
        return ((OrientedPoint) node.getCut().getHyperplane()).isDirect();
    }

    /** Get the abscissa of an internal node.
     * @param node internal node to check
     * @return abscissa
     */
    private double getAngle(final BSPTree<Euclidean1D> node) {
        return ((OrientedPoint) node.getCut().getHyperplane()).getLocation().getX();
    }

    /** {@inheritDoc}
     * <p>
     * The iterator returns the limit values of sub-intervals in ascending order.
     * </p>
     * <p>
     * The iterator does <em>not</em> support the optional {@code remove} operation.
     * </p>
     * @since 3.3
     */
    public Iterator<double[]> iterator() {
        return new SubIntervalsIterator();
    }

    /** Local iterator for sub-intervals. */
    private class SubIntervalsIterator implements Iterator<double[]> {

        /** Current node. */
        private BSPTree<Euclidean1D> current;

        /** Sub-interval no yet returned. */
        private double[] pending;

        /** Simple constructor.
         */
        SubIntervalsIterator() {

            current = getFirstIntervalBoundary();

            if (current == null) {
                // all the leaf tree nodes share the same inside/outside status
                if ((Boolean) getFirstLeaf(getTree(false)).getAttribute()) {
                    // it is an inside node, it represents the full real line
                    pending = new double[] {
                        Double.NEGATIVE_INFINITY, Double.POSITIVE_INFINITY
                    };
                } else {
                    pending = null;
                }
            } else if (isIntervalEnd(current)) {
                // the first boundary is an interval end,
                // so the first interval starts at infinity
                pending = new double[] {
                    Double.NEGATIVE_INFINITY, getAngle(current)
                };
            } else {
                selectPending();
            }
        }

        /** Walk the tree to select the pending sub-interval.
         */
        private void selectPending() {

            // look for the start of the interval
            BSPTree<Euclidean1D> start = current;
            while (start != null && !isIntervalStart(start)) {
                start = nextInternalNode(start);
            }

            if (start == null) {
                // we have exhausted the iterator
                current = null;
                pending = null;
                return;
            }

            // look for the end of the interval
            BSPTree<Euclidean1D> end = start;
            while (end != null && !isIntervalEnd(end)) {
                end = nextInternalNode(end);
            }

            if (end != null) {

                // we have identified the interval
                pending = new double[] {
                    getAngle(start), getAngle(end)
                };

                // prepare search for next interval
                current = end;

            } else {

                // the final interval is open toward infinity
                pending = new double[] {
                    getAngle(start), Double.POSITIVE_INFINITY
                };

                // there won't be any other intervals
                current = null;

            }

        }

        /** {@inheritDoc} */
        public boolean hasNext() {
            return pending != null;
        }

        /** {@inheritDoc} */
        public double[] next() {
            if (pending == null) {
                throw new NoSuchElementException();
            }
            final double[] next = pending;
            selectPending();
            return next;
        }

        /** {@inheritDoc} */
        public void remove() {
            throw new UnsupportedOperationException();
        }

    }

}
