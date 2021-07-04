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
import org.apache.commons.math3.geometry.Point;

/** This interface represents a region of a space as a partition.

 * <p>Region are subsets of a space, they can be infinite (whole
 * space, half space, infinite stripe ...) or finite (polygons in 2D,
 * polyhedrons in 3D ...). Their main characteristic is to separate
 * points that are considered to be <em>inside</em> the region from
 * points considered to be <em>outside</em> of it. In between, there
 * may be points on the <em>boundary</em> of the region.</p>

 * <p>This implementation is limited to regions for which the boundary
 * is composed of several {@link SubHyperplane sub-hyperplanes},
 * including regions with no boundary at all: the whole space and the
 * empty region. They are not necessarily finite and not necessarily
 * path-connected. They can contain holes.</p>

 * <p>Regions can be combined using the traditional sets operations :
 * union, intersection, difference and symetric difference (exclusive
 * or) for the binary operations, complement for the unary
 * operation.</p>

 * <p>
 * Note that this interface is <em>not</em> intended to be implemented
 * by Apache Commons Math users, it is only intended to be implemented
 * within the library itself. New methods may be added even for minor
 * versions, which breaks compatibility for external implementations.
 * </p>

 * @param <S> Type of the space.

 * @since 3.0
 */
public interface Region<S extends Space> {

    /** Enumerate for the location of a point with respect to the region. */
    enum Location {
        /** Code for points inside the partition. */
        INSIDE,

        /** Code for points outside of the partition. */
        OUTSIDE,

        /** Code for points on the partition boundary. */
        BOUNDARY;
    }

    /** Build a region using the instance as a prototype.
     * <p>This method allow to create new instances without knowing
     * exactly the type of the region. It is an application of the
     * prototype design pattern.</p>
     * <p>The leaf nodes of the BSP tree <em>must</em> have a
     * {@code Boolean} attribute representing the inside status of
     * the corresponding cell (true for inside cells, false for outside
     * cells). In order to avoid building too many small objects, it is
     * recommended to use the predefined constants
     * {@code Boolean.TRUE} and {@code Boolean.FALSE}. The
     * tree also <em>must</em> have either null internal nodes or
     * internal nodes representing the boundary as specified in the
     * {@link #getTree getTree} method).</p>
     * @param newTree inside/outside BSP tree representing the new region
     * @return the built region
     */
    Region<S> buildNew(BSPTree<S> newTree);

    /** Copy the instance.
     * <p>The instance created is completely independant of the original
     * one. A deep copy is used, none of the underlying objects are
     * shared (except for the underlying tree {@code Boolean}
     * attributes and immutable objects).</p>
     * @return a new region, copy of the instance
     */
    Region<S> copySelf();

    /** Check if the instance is empty.
     * @return true if the instance is empty
     */
    boolean isEmpty();

    /** Check if the sub-tree starting at a given node is empty.
     * @param node root node of the sub-tree (<em>must</em> have {@link
     * Region Region} tree semantics, i.e. the leaf nodes must have
     * {@code Boolean} attributes representing an inside/outside
     * property)
     * @return true if the sub-tree starting at the given node is empty
     */
    boolean isEmpty(final BSPTree<S> node);

    /** Check if the instance covers the full space.
     * @return true if the instance covers the full space
     */
    boolean isFull();

    /** Check if the sub-tree starting at a given node covers the full space.
     * @param node root node of the sub-tree (<em>must</em> have {@link
     * Region Region} tree semantics, i.e. the leaf nodes must have
     * {@code Boolean} attributes representing an inside/outside
     * property)
     * @return true if the sub-tree starting at the given node covers the full space
     */
    boolean isFull(final BSPTree<S> node);

    /** Check if the instance entirely contains another region.
     * @param region region to check against the instance
     * @return true if the instance contains the specified tree
     */
    boolean contains(final Region<S> region);

    /** Check a point with respect to the region.
     * @param point point to check
     * @return a code representing the point status: either {@link
     * Location#INSIDE}, {@link Location#OUTSIDE} or {@link Location#BOUNDARY}
     */
    Location checkPoint(final Point<S> point);

    /** Project a point on the boundary of the region.
     * @param point point to check
     * @return projection of the point on the boundary
     * @since 3.3
     */
    BoundaryProjection<S> projectToBoundary(final Point<S> point);

    /** Get the underlying BSP tree.

     * <p>Regions are represented by an underlying inside/outside BSP
     * tree whose leaf attributes are {@code Boolean} instances
     * representing inside leaf cells if the attribute value is
     * {@code true} and outside leaf cells if the attribute is
     * {@code false}. These leaf attributes are always present and
     * guaranteed to be non null.</p>

     * <p>In addition to the leaf attributes, the internal nodes which
     * correspond to cells split by cut sub-hyperplanes may contain
     * {@link BoundaryAttribute BoundaryAttribute} objects representing
     * the parts of the corresponding cut sub-hyperplane that belong to
     * the boundary. When the boundary attributes have been computed,
     * all internal nodes are guaranteed to have non-null
     * attributes, however some {@link BoundaryAttribute
     * BoundaryAttribute} instances may have their {@link
     * BoundaryAttribute#getPlusInside() getPlusInside} and {@link
     * BoundaryAttribute#getPlusOutside() getPlusOutside} methods both
     * returning null if the corresponding cut sub-hyperplane does not
     * have any parts belonging to the boundary.</p>

     * <p>Since computing the boundary is not always required and can be
     * time-consuming for large trees, these internal nodes attributes
     * are computed using lazy evaluation only when required by setting
     * the {@code includeBoundaryAttributes} argument to
     * {@code true}. Once computed, these attributes remain in the
     * tree, which implies that in this case, further calls to the
     * method for the same region will always include these attributes
     * regardless of the value of the
     * {@code includeBoundaryAttributes} argument.</p>

     * @param includeBoundaryAttributes if true, the boundary attributes
     * at internal nodes are guaranteed to be included (they may be
     * included even if the argument is false, if they have already been
     * computed due to a previous call)
     * @return underlying BSP tree
     * @see BoundaryAttribute
     */
    BSPTree<S> getTree(final boolean includeBoundaryAttributes);

    /** Get the size of the boundary.
     * @return the size of the boundary (this is 0 in 1D, a length in
     * 2D, an area in 3D ...)
     */
    double getBoundarySize();

    /** Get the size of the instance.
     * @return the size of the instance (this is a length in 1D, an area
     * in 2D, a volume in 3D ...)
     */
    double getSize();

    /** Get the barycenter of the instance.
     * @return an object representing the barycenter
     */
    Point<S> getBarycenter();

    /** Compute the relative position of the instance with respect to an
     * hyperplane.
     * @param hyperplane reference hyperplane
     * @return one of {@link Side#PLUS Side.PLUS}, {@link Side#MINUS
     * Side.MINUS}, {@link Side#BOTH Side.BOTH} or {@link Side#HYPER
     * Side.HYPER} (the latter result can occur only if the tree
     * contains only one cut hyperplane)
     * @deprecated as of 3.6, this method which was only intended for
     * internal use is not used anymore
     */
    @Deprecated
    Side side(final Hyperplane<S> hyperplane);

    /** Get the parts of a sub-hyperplane that are contained in the region.
     * <p>The parts of the sub-hyperplane that belong to the boundary are
     * <em>not</em> included in the resulting parts.</p>
     * @param sub sub-hyperplane traversing the region
     * @return filtered sub-hyperplane
     */
    SubHyperplane<S> intersection(final SubHyperplane<S> sub);

}
