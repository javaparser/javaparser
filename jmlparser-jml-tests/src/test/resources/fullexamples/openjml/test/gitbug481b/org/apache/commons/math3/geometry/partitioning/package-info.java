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
/**
 *
 * This package provides classes to implement Binary Space Partition trees.
 *
 * <p>
 * {@link org.apache.commons.math3.geometry.partitioning.BSPTree BSP trees}
 * are an efficient way to represent parts of space and in particular
 * polytopes (line segments in 1D, polygons in 2D and polyhedrons in 3D)
 * and to operate on them. The main principle is to recursively subdivide
 * the space using simple hyperplanes (points in 1D, lines in 2D, planes
 * in 3D).
 * </p>
 *
 * <p>
 * We start with a tree composed of a single node without any cut
 * hyperplane: it represents the complete space, which is a convex
 * part. If we add a cut hyperplane to this node, this represents a
 * partition with the hyperplane at the node level and two half spaces at
 * each side of the cut hyperplane. These half-spaces are represented by
 * two child nodes without any cut hyperplanes associated, the plus child
 * which represents the half space on the plus side of the cut hyperplane
 * and the minus child on the other side. Continuing the subdivisions, we
 * end up with a tree having internal nodes that are associated with a
 * cut hyperplane and leaf nodes without any hyperplane which correspond
 * to convex parts.
 * </p>
 *
 * <p>
 * When BSP trees are used to represent polytopes, the convex parts are
 * known to be completely inside or outside the polytope as long as there
 * is no facet in the part (which is obviously the case if the cut
 * hyperplanes have been chosen as the underlying hyperplanes of the
 * facets (this is called an autopartition) and if the subdivision
 * process has been continued until all facets have been processed. It is
 * important to note that the polytope is <em>not</em> defined by a
 * single part, but by several convex ones. This is the property that
 * allows BSP-trees to represent non-convex polytopes despites all parts
 * are convex. The {@link
 * org.apache.commons.math3.geometry.partitioning.Region Region} class is
 * devoted to this representation, it is build on top of the {@link
 * org.apache.commons.math3.geometry.partitioning.BSPTree BSPTree} class using
 * boolean objects as the leaf nodes attributes to represent the
 * inside/outside property of each leaf part, and also adds various
 * methods dealing with boundaries (i.e. the separation between the
 * inside and the outside parts).
 * </p>
 *
 * <p>
 * Rather than simply associating the internal nodes with an hyperplane,
 * we consider <em>sub-hyperplanes</em> which correspond to the part of
 * the hyperplane that is inside the convex part defined by all the
 * parent nodes (this implies that the sub-hyperplane at root node is in
 * fact a complete hyperplane, because there is no parent to bound
 * it). Since the parts are convex, the sub-hyperplanes are convex, in
 * 3D the convex parts are convex polyhedrons, and the sub-hyperplanes
 * are convex polygons that cut these polyhedrons in two
 * sub-polyhedrons. Using this definition, a BSP tree completely
 * partitions the space. Each point either belongs to one of the
 * sub-hyperplanes in an internal node or belongs to one of the leaf
 * convex parts.
 * </p>
 *
 * <p>
 * In order to determine where a point is, it is sufficient to check its
 * position with respect to the root cut hyperplane, to select the
 * corresponding child tree and to repeat the procedure recursively,
 * until either the point appears to be exactly on one of the hyperplanes
 * in the middle of the tree or to be in one of the leaf parts. For
 * this operation, it is sufficient to consider the complete hyperplanes,
 * there is no need to check the points with the boundary of the
 * sub-hyperplanes, because this check has in fact already been realized
 * by the recursive descent in the tree. This is very easy to do and very
 * efficient, especially if the tree is well balanced (the cost is
 * <code>O(log(n))</code> where <code>n</code> is the number of facets)
 * or if the first tree levels close to the root discriminate large parts
 * of the total space.
 * </p>
 *
 * <p>
 * One of the main sources for the development of this package was Bruce
 * Naylor, John Amanatides and William Thibault paper <a
 * href="http://www.cs.yorku.ca/~amana/research/bsptSetOp.pdf">Merging
 * BSP Trees Yields Polyhedral Set Operations</a> Proc. Siggraph '90,
 * Computer Graphics 24(4), August 1990, pp 115-124, published by the
 * Association for Computing Machinery (ACM). The same paper can also be
 * found <a
 * href="http://www.cs.utexas.edu/users/fussell/courses/cs384g/bsp_treemerge.pdf">here</a>.
 * </p>
 *
 * <p>
 * Note that the interfaces defined in this package are <em>not</em> intended to
 * be implemented by Apache Commons Math users, they are only intended to be
 * implemented within the library itself. New methods may be added even for
 * minor versions, which breaks compatibility for external implementations.
 * </p>
 *
 */
package org.apache.commons.math3.geometry.partitioning;
