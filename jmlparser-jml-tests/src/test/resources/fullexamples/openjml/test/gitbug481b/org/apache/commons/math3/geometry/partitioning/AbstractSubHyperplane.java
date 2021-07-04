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

import java.util.HashMap;
import java.util.Map;

import org.apache.commons.math3.geometry.Space;

/** This class implements the dimension-independent parts of {@link SubHyperplane}.

 * <p>sub-hyperplanes are obtained when parts of an {@link
 * Hyperplane hyperplane} are chopped off by other hyperplanes that
 * intersect it. The remaining part is a convex region. Such objects
 * appear in {@link BSPTree BSP trees} as the intersection of a cut
 * hyperplane with the convex region which it splits, the chopping
 * hyperplanes are the cut hyperplanes closer to the tree root.</p>

 * @param <S> Type of the embedding space.
 * @param <T> Type of the embedded sub-space.

 * @since 3.0
 */
public abstract class AbstractSubHyperplane<S extends Space, T extends Space>
    implements SubHyperplane<S> {

    /** Underlying hyperplane. */
    private final Hyperplane<S> hyperplane;

    /** Remaining region of the hyperplane. */
    private final Region<T> remainingRegion;

    /** Build a sub-hyperplane from an hyperplane and a region.
     * @param hyperplane underlying hyperplane
     * @param remainingRegion remaining region of the hyperplane
     */
    protected AbstractSubHyperplane(final Hyperplane<S> hyperplane,
                                    final Region<T> remainingRegion) {
        this.hyperplane      = hyperplane;
        this.remainingRegion = remainingRegion;
    }

    /** Build a sub-hyperplane from an hyperplane and a region.
     * @param hyper underlying hyperplane
     * @param remaining remaining region of the hyperplane
     * @return a new sub-hyperplane
     */
    protected abstract AbstractSubHyperplane<S, T> buildNew(final Hyperplane<S> hyper,
                                                            final Region<T> remaining);

    /** {@inheritDoc} */
    public AbstractSubHyperplane<S, T> copySelf() {
        return buildNew(hyperplane.copySelf(), remainingRegion);
    }

    /** Get the underlying hyperplane.
     * @return underlying hyperplane
     */
    public Hyperplane<S> getHyperplane() {
        return hyperplane;
    }

    /** Get the remaining region of the hyperplane.
     * <p>The returned region is expressed in the canonical hyperplane
     * frame and has the hyperplane dimension. For example a chopped
     * hyperplane in the 3D euclidean is a 2D plane and the
     * corresponding region is a convex 2D polygon.</p>
     * @return remaining region of the hyperplane
     */
    public Region<T> getRemainingRegion() {
        return remainingRegion;
    }

    /** {@inheritDoc} */
    public double getSize() {
        return remainingRegion.getSize();
    }

    /** {@inheritDoc} */
    public AbstractSubHyperplane<S, T> reunite(final SubHyperplane<S> other) {
        @SuppressWarnings("unchecked")
        AbstractSubHyperplane<S, T> o = (AbstractSubHyperplane<S, T>) other;
        return buildNew(hyperplane,
                        new RegionFactory<T>().union(remainingRegion, o.remainingRegion));
    }

    /** Apply a transform to the instance.
     * <p>The instance must be a (D-1)-dimension sub-hyperplane with
     * respect to the transform <em>not</em> a (D-2)-dimension
     * sub-hyperplane the transform knows how to transform by
     * itself. The transform will consist in transforming first the
     * hyperplane and then the all region using the various methods
     * provided by the transform.</p>
     * @param transform D-dimension transform to apply
     * @return the transformed instance
     */
    public AbstractSubHyperplane<S, T> applyTransform(final Transform<S, T> transform) {
        final Hyperplane<S> tHyperplane = transform.apply(hyperplane);

        // transform the tree, except for boundary attribute splitters
        final Map<BSPTree<T>, BSPTree<T>> map = new HashMap<BSPTree<T>, BSPTree<T>>();
        final BSPTree<T> tTree =
            recurseTransform(remainingRegion.getTree(false), tHyperplane, transform, map);

        // set up the boundary attributes splitters
        for (final Map.Entry<BSPTree<T>, BSPTree<T>> entry : map.entrySet()) {
            if (entry.getKey().getCut() != null) {
                @SuppressWarnings("unchecked")
                BoundaryAttribute<T> original = (BoundaryAttribute<T>) entry.getKey().getAttribute();
                if (original != null) {
                    @SuppressWarnings("unchecked")
                    BoundaryAttribute<T> transformed = (BoundaryAttribute<T>) entry.getValue().getAttribute();
                    for (final BSPTree<T> splitter : original.getSplitters()) {
                        transformed.getSplitters().add(map.get(splitter));
                    }
                }
            }
        }

        return buildNew(tHyperplane, remainingRegion.buildNew(tTree));

    }

    /** Recursively transform a BSP-tree from a sub-hyperplane.
     * @param node current BSP tree node
     * @param transformed image of the instance hyperplane by the transform
     * @param transform transform to apply
     * @param map transformed nodes map
     * @return a new tree
     */
    private BSPTree<T> recurseTransform(final BSPTree<T> node,
                                        final Hyperplane<S> transformed,
                                        final Transform<S, T> transform,
                                        final Map<BSPTree<T>, BSPTree<T>> map) {

        final BSPTree<T> transformedNode;
        if (node.getCut() == null) {
            transformedNode = new BSPTree<T>(node.getAttribute());
        } else {

            @SuppressWarnings("unchecked")
            BoundaryAttribute<T> attribute = (BoundaryAttribute<T>) node.getAttribute();
            if (attribute != null) {
                final SubHyperplane<T> tPO = (attribute.getPlusOutside() == null) ?
                    null : transform.apply(attribute.getPlusOutside(), hyperplane, transformed);
                final SubHyperplane<T> tPI = (attribute.getPlusInside() == null) ?
                    null : transform.apply(attribute.getPlusInside(), hyperplane, transformed);
                // we start with an empty list of splitters, it will be filled in out of recursion
                attribute = new BoundaryAttribute<T>(tPO, tPI, new NodesSet<T>());
            }

            transformedNode = new BSPTree<T>(transform.apply(node.getCut(), hyperplane, transformed),
                    recurseTransform(node.getPlus(),  transformed, transform, map),
                    recurseTransform(node.getMinus(), transformed, transform, map),
                    attribute);
        }

        map.put(node, transformedNode);
        return transformedNode;

    }

    /** {@inheritDoc} */
    @Deprecated
    public Side side(Hyperplane<S> hyper) {
        return split(hyper).getSide();
    }

    /** {@inheritDoc} */
    public abstract SplitSubHyperplane<S> split(Hyperplane<S> hyper);

    /** {@inheritDoc} */
    public boolean isEmpty() {
        return remainingRegion.isEmpty();
    }

}
