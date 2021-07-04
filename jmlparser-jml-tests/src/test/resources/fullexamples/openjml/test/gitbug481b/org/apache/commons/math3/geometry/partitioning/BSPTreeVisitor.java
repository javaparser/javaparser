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

import org.apache.commons.math3.geometry.Space;

/** This interface is used to visit {@link BSPTree BSP tree} nodes.

 * <p>Navigation through {@link BSPTree BSP trees} can be done using
 * two different point of views:</p>
 * <ul>
 *   <li>
 *     the first one is in a node-oriented way using the {@link
 *     BSPTree#getPlus}, {@link BSPTree#getMinus} and {@link
 *     BSPTree#getParent} methods. Terminal nodes without associated
 *     {@link SubHyperplane sub-hyperplanes} can be visited this way,
 *     there is no constraint in the visit order, and it is possible
 *     to visit either all nodes or only a subset of the nodes
 *   </li>
 *   <li>
 *     the second one is in a sub-hyperplane-oriented way using
 *     classes implementing this interface which obeys the visitor
 *     design pattern. The visit order is provided by the visitor as
 *     each node is first encountered. Each node is visited exactly
 *     once.
 *   </li>
 * </ul>

 * @param <S> Type of the space.

 * @see BSPTree
 * @see SubHyperplane

 * @since 3.0
 */
public interface BSPTreeVisitor<S extends Space> {

    /** Enumerate for visit order with respect to plus sub-tree, minus sub-tree and cut sub-hyperplane. */
    enum Order {
        /** Indicator for visit order plus sub-tree, then minus sub-tree,
         * and last cut sub-hyperplane.
         */
        PLUS_MINUS_SUB,

        /** Indicator for visit order plus sub-tree, then cut sub-hyperplane,
         * and last minus sub-tree.
         */
        PLUS_SUB_MINUS,

        /** Indicator for visit order minus sub-tree, then plus sub-tree,
         * and last cut sub-hyperplane.
         */
        MINUS_PLUS_SUB,

        /** Indicator for visit order minus sub-tree, then cut sub-hyperplane,
         * and last plus sub-tree.
         */
        MINUS_SUB_PLUS,

        /** Indicator for visit order cut sub-hyperplane, then plus sub-tree,
         * and last minus sub-tree.
         */
        SUB_PLUS_MINUS,

        /** Indicator for visit order cut sub-hyperplane, then minus sub-tree,
         * and last plus sub-tree.
         */
        SUB_MINUS_PLUS;
    }

    /** Determine the visit order for this node.
     * <p>Before attempting to visit an internal node, this method is
     * called to determine the desired ordering of the visit. It is
     * guaranteed that this method will be called before {@link
     * #visitInternalNode visitInternalNode} for a given node, it will be
     * called exactly once for each internal node.</p>
     * @param node BSP node guaranteed to have a non null cut sub-hyperplane
     * @return desired visit order, must be one of
     * {@link Order#PLUS_MINUS_SUB}, {@link Order#PLUS_SUB_MINUS},
     * {@link Order#MINUS_PLUS_SUB}, {@link Order#MINUS_SUB_PLUS},
     * {@link Order#SUB_PLUS_MINUS}, {@link Order#SUB_MINUS_PLUS}
     */
    Order visitOrder(BSPTree<S> node);

    /** Visit a BSP tree node node having a non-null sub-hyperplane.
     * <p>It is guaranteed that this method will be called after {@link
     * #visitOrder visitOrder} has been called for a given node,
     * it wil be called exactly once for each internal node.</p>
     * @param node BSP node guaranteed to have a non null cut sub-hyperplane
     * @see #visitLeafNode
     */
    void visitInternalNode(BSPTree<S> node);

    /** Visit a leaf BSP tree node node having a null sub-hyperplane.
     * @param node leaf BSP node having a null sub-hyperplane
     * @see #visitInternalNode
     */
    void visitLeafNode(BSPTree<S> node);

}
