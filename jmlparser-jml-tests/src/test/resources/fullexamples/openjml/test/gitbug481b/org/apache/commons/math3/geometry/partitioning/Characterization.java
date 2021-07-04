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

import org.apache.commons.math3.exception.MathInternalError;
import org.apache.commons.math3.geometry.Space;

/** Cut sub-hyperplanes characterization with respect to inside/outside cells.
 * @see BoundaryBuilder
 * @param <S> Type of the space.
 * @since 3.4
 */
class Characterization<S extends Space> {

    /** Part of the cut sub-hyperplane that touch outside cells. */
    private SubHyperplane<S> outsideTouching;

    /** Part of the cut sub-hyperplane that touch inside cells. */
    private SubHyperplane<S> insideTouching;

    /** Nodes that were used to split the outside touching part. */
    private final NodesSet<S> outsideSplitters;

    /** Nodes that were used to split the outside touching part. */
    private final NodesSet<S> insideSplitters;

    /** Simple constructor.
     * <p>Characterization consists in splitting the specified
     * sub-hyperplane into several parts lying in inside and outside
     * cells of the tree. The principle is to compute characterization
     * twice for each cut sub-hyperplane in the tree, once on the plus
     * node and once on the minus node. The parts that have the same flag
     * (inside/inside or outside/outside) do not belong to the boundary
     * while parts that have different flags (inside/outside or
     * outside/inside) do belong to the boundary.</p>
     * @param node current BSP tree node
     * @param sub sub-hyperplane to characterize
     */
    Characterization(final BSPTree<S> node, final SubHyperplane<S> sub) {
        outsideTouching  = null;
        insideTouching   = null;
        outsideSplitters = new NodesSet<S>();
        insideSplitters  = new NodesSet<S>();
        characterize(node, sub, new ArrayList<BSPTree<S>>());
    }

    /** Filter the parts of an hyperplane belonging to the boundary.
     * <p>The filtering consist in splitting the specified
     * sub-hyperplane into several parts lying in inside and outside
     * cells of the tree. The principle is to call this method twice for
     * each cut sub-hyperplane in the tree, once on the plus node and
     * once on the minus node. The parts that have the same flag
     * (inside/inside or outside/outside) do not belong to the boundary
     * while parts that have different flags (inside/outside or
     * outside/inside) do belong to the boundary.</p>
     * @param node current BSP tree node
     * @param sub sub-hyperplane to characterize
     * @param splitters nodes that did split the current one
     */
    private void characterize(final BSPTree<S> node, final SubHyperplane<S> sub,
                              final List<BSPTree<S>> splitters) {
        if (node.getCut() == null) {
            // we have reached a leaf node
            final boolean inside = (Boolean) node.getAttribute();
            if (inside) {
                addInsideTouching(sub, splitters);
            } else {
                addOutsideTouching(sub, splitters);
            }
        } else {
            final Hyperplane<S> hyperplane = node.getCut().getHyperplane();
            final SubHyperplane.SplitSubHyperplane<S> split = sub.split(hyperplane);
            switch (split.getSide()) {
            case PLUS:
                characterize(node.getPlus(),  sub, splitters);
                break;
            case MINUS:
                characterize(node.getMinus(), sub, splitters);
                break;
            case BOTH:
                splitters.add(node);
                characterize(node.getPlus(),  split.getPlus(),  splitters);
                characterize(node.getMinus(), split.getMinus(), splitters);
                splitters.remove(splitters.size() - 1);
                break;
            default:
                // this should not happen
                throw new MathInternalError();
            }
        }
    }

    /** Add a part of the cut sub-hyperplane known to touch an outside cell.
     * @param sub part of the cut sub-hyperplane known to touch an outside cell
     * @param splitters sub-hyperplanes that did split the current one
     */
    private void addOutsideTouching(final SubHyperplane<S> sub,
                                    final List<BSPTree<S>> splitters) {
        if (outsideTouching == null) {
            outsideTouching = sub;
        } else {
            outsideTouching = outsideTouching.reunite(sub);
        }
        outsideSplitters.addAll(splitters);
    }

    /** Add a part of the cut sub-hyperplane known to touch an inside cell.
     * @param sub part of the cut sub-hyperplane known to touch an inside cell
     * @param splitters sub-hyperplanes that did split the current one
     */
    private void addInsideTouching(final SubHyperplane<S> sub,
                                   final List<BSPTree<S>> splitters) {
        if (insideTouching == null) {
            insideTouching = sub;
        } else {
            insideTouching = insideTouching.reunite(sub);
        }
        insideSplitters.addAll(splitters);
    }

    /** Check if the cut sub-hyperplane touches outside cells.
     * @return true if the cut sub-hyperplane touches outside cells
     */
    public boolean touchOutside() {
        return outsideTouching != null && !outsideTouching.isEmpty();
    }

    /** Get all the parts of the cut sub-hyperplane known to touch outside cells.
     * @return parts of the cut sub-hyperplane known to touch outside cells
     * (may be null or empty)
     */
    public SubHyperplane<S> outsideTouching() {
        return outsideTouching;
    }

    /** Get the nodes that were used to split the outside touching part.
     * <p>
     * Splitting nodes are internal nodes (i.e. they have a non-null
     * cut sub-hyperplane).
     * </p>
     * @return nodes that were used to split the outside touching part
     */
    public NodesSet<S> getOutsideSplitters() {
        return outsideSplitters;
    }

    /** Check if the cut sub-hyperplane touches inside cells.
     * @return true if the cut sub-hyperplane touches inside cells
     */
    public boolean touchInside() {
        return insideTouching != null && !insideTouching.isEmpty();
    }

    /** Get all the parts of the cut sub-hyperplane known to touch inside cells.
     * @return parts of the cut sub-hyperplane known to touch inside cells
     * (may be null or empty)
     */
    public SubHyperplane<S> insideTouching() {
        return insideTouching;
    }

    /** Get the nodes that were used to split the inside touching part.
     * <p>
     * Splitting nodes are internal nodes (i.e. they have a non-null
     * cut sub-hyperplane).
     * </p>
     * @return nodes that were used to split the inside touching part
     */
    public NodesSet<S> getInsideSplitters() {
        return insideSplitters;
    }

}
