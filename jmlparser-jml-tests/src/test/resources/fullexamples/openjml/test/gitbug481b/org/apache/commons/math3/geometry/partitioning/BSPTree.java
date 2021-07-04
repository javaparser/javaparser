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

import org.apache.commons.math3.exception.MathIllegalStateException;
import org.apache.commons.math3.exception.MathInternalError;
import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.geometry.Point;
import org.apache.commons.math3.geometry.Space;
import org.apache.commons.math3.geometry.Vector;
import org.apache.commons.math3.util.FastMath;

/** This class represent a Binary Space Partition tree.

 * <p>BSP trees are an efficient way to represent space partitions and
 * to associate attributes with each cell. Each node in a BSP tree
 * represents a convex region which is partitioned in two convex
 * sub-regions at each side of a cut hyperplane. The root tree
 * contains the complete space.</p>

 * <p>The main use of such partitions is to use a boolean attribute to
 * define an inside/outside property, hence representing arbitrary
 * polytopes (line segments in 1D, polygons in 2D and polyhedrons in
 * 3D) and to operate on them.</p>

 * <p>Another example would be to represent Voronoi tesselations, the
 * attribute of each cell holding the defining point of the cell.</p>

 * <p>The application-defined attributes are shared among copied
 * instances and propagated to split parts. These attributes are not
 * used by the BSP-tree algorithms themselves, so the application can
 * use them for any purpose. Since the tree visiting method holds
 * internal and leaf nodes differently, it is possible to use
 * different classes for internal nodes attributes and leaf nodes
 * attributes. This should be used with care, though, because if the
 * tree is modified in any way after attributes have been set, some
 * internal nodes may become leaf nodes and some leaf nodes may become
 * internal nodes.</p>

 * <p>One of the main sources for the development of this package was
 * Bruce Naylor, John Amanatides and William Thibault paper <a
 * href="http://www.cs.yorku.ca/~amana/research/bsptSetOp.pdf">Merging
 * BSP Trees Yields Polyhedral Set Operations</a> Proc. Siggraph '90,
 * Computer Graphics 24(4), August 1990, pp 115-124, published by the
 * Association for Computing Machinery (ACM).</p>

 * @param <S> Type of the space.

 * @since 3.0
 */
public class BSPTree<S extends Space> {

    /** Cut sub-hyperplane. */
    private SubHyperplane<S> cut;

    /** Tree at the plus side of the cut hyperplane. */
    private BSPTree<S> plus;

    /** Tree at the minus side of the cut hyperplane. */
    private BSPTree<S> minus;

    /** Parent tree. */
    private BSPTree<S> parent;

    /** Application-defined attribute. */
    private Object attribute;

    /** Build a tree having only one root cell representing the whole space.
     */
    public BSPTree() {
        cut       = null;
        plus      = null;
        minus     = null;
        parent    = null;
        attribute = null;
    }

    /** Build a tree having only one root cell representing the whole space.
     * @param attribute attribute of the tree (may be null)
     */
    public BSPTree(final Object attribute) {
        cut    = null;
        plus   = null;
        minus  = null;
        parent = null;
        this.attribute = attribute;
    }

    /** Build a BSPTree from its underlying elements.
     * <p>This method does <em>not</em> perform any verification on
     * consistency of its arguments, it should therefore be used only
     * when then caller knows what it is doing.</p>
     * <p>This method is mainly useful to build trees
     * bottom-up. Building trees top-down is realized with the help of
     * method {@link #insertCut insertCut}.</p>
     * @param cut cut sub-hyperplane for the tree
     * @param plus plus side sub-tree
     * @param minus minus side sub-tree
     * @param attribute attribute associated with the node (may be null)
     * @see #insertCut
     */
    public BSPTree(final SubHyperplane<S> cut, final BSPTree<S> plus, final BSPTree<S> minus,
                   final Object attribute) {
        this.cut       = cut;
        this.plus      = plus;
        this.minus     = minus;
        this.parent    = null;
        this.attribute = attribute;
        plus.parent    = this;
        minus.parent   = this;
    }

    /** Insert a cut sub-hyperplane in a node.
     * <p>The sub-tree starting at this node will be completely
     * overwritten. The new cut sub-hyperplane will be built from the
     * intersection of the provided hyperplane with the cell. If the
     * hyperplane does intersect the cell, the cell will have two
     * children cells with {@code null} attributes on each side of
     * the inserted cut sub-hyperplane. If the hyperplane does not
     * intersect the cell then <em>no</em> cut hyperplane will be
     * inserted and the cell will be changed to a leaf cell. The
     * attribute of the node is never changed.</p>
     * <p>This method is mainly useful when called on leaf nodes
     * (i.e. nodes for which {@link #getCut getCut} returns
     * {@code null}), in this case it provides a way to build a
     * tree top-down (whereas the {@link #BSPTree(SubHyperplane,
     * BSPTree, BSPTree, Object) 4 arguments constructor} is devoted to
     * build trees bottom-up).</p>
     * @param hyperplane hyperplane to insert, it will be chopped in
     * order to fit in the cell defined by the parent nodes of the
     * instance
     * @return true if a cut sub-hyperplane has been inserted (i.e. if
     * the cell now has two leaf child nodes)
     * @see #BSPTree(SubHyperplane, BSPTree, BSPTree, Object)
     */
    public boolean insertCut(final Hyperplane<S> hyperplane) {

        if (cut != null) {
            plus.parent  = null;
            minus.parent = null;
        }

        final SubHyperplane<S> chopped = fitToCell(hyperplane.wholeHyperplane());
        if (chopped == null || chopped.isEmpty()) {
            cut          = null;
            plus         = null;
            minus        = null;
            return false;
        }

        cut          = chopped;
        plus         = new BSPTree<S>();
        plus.parent  = this;
        minus        = new BSPTree<S>();
        minus.parent = this;
        return true;

    }

    /** Copy the instance.
     * <p>The instance created is completely independent of the original
     * one. A deep copy is used, none of the underlying objects are
     * shared (except for the nodes attributes and immutable
     * objects).</p>
     * @return a new tree, copy of the instance
     */
    public BSPTree<S> copySelf() {

        if (cut == null) {
            return new BSPTree<S>(attribute);
        }

        return new BSPTree<S>(cut.copySelf(), plus.copySelf(), minus.copySelf(),
                           attribute);

    }

    /** Get the cut sub-hyperplane.
     * @return cut sub-hyperplane, null if this is a leaf tree
     */
    public SubHyperplane<S> getCut() {
        return cut;
    }

    /** Get the tree on the plus side of the cut hyperplane.
     * @return tree on the plus side of the cut hyperplane, null if this
     * is a leaf tree
     */
    public BSPTree<S> getPlus() {
        return plus;
    }

    /** Get the tree on the minus side of the cut hyperplane.
     * @return tree on the minus side of the cut hyperplane, null if this
     * is a leaf tree
     */
    public BSPTree<S> getMinus() {
        return minus;
    }

    /** Get the parent node.
     * @return parent node, null if the node has no parents
     */
    public BSPTree<S> getParent() {
        return parent;
    }

    /** Associate an attribute with the instance.
     * @param attribute attribute to associate with the node
     * @see #getAttribute
     */
    public void setAttribute(final Object attribute) {
        this.attribute = attribute;
    }

    /** Get the attribute associated with the instance.
     * @return attribute associated with the node or null if no
     * attribute has been explicitly set using the {@link #setAttribute
     * setAttribute} method
     * @see #setAttribute
     */
    public Object getAttribute() {
        return attribute;
    }

    /** Visit the BSP tree nodes.
     * @param visitor object visiting the tree nodes
     */
    public void visit(final BSPTreeVisitor<S> visitor) {
        if (cut == null) {
            visitor.visitLeafNode(this);
        } else {
            switch (visitor.visitOrder(this)) {
            case PLUS_MINUS_SUB:
                plus.visit(visitor);
                minus.visit(visitor);
                visitor.visitInternalNode(this);
                break;
            case PLUS_SUB_MINUS:
                plus.visit(visitor);
                visitor.visitInternalNode(this);
                minus.visit(visitor);
                break;
            case MINUS_PLUS_SUB:
                minus.visit(visitor);
                plus.visit(visitor);
                visitor.visitInternalNode(this);
                break;
            case MINUS_SUB_PLUS:
                minus.visit(visitor);
                visitor.visitInternalNode(this);
                plus.visit(visitor);
                break;
            case SUB_PLUS_MINUS:
                visitor.visitInternalNode(this);
                plus.visit(visitor);
                minus.visit(visitor);
                break;
            case SUB_MINUS_PLUS:
                visitor.visitInternalNode(this);
                minus.visit(visitor);
                plus.visit(visitor);
                break;
            default:
                throw new MathInternalError();
            }

        }
    }

    /** Fit a sub-hyperplane inside the cell defined by the instance.
     * <p>Fitting is done by chopping off the parts of the
     * sub-hyperplane that lie outside of the cell using the
     * cut-hyperplanes of the parent nodes of the instance.</p>
     * @param sub sub-hyperplane to fit
     * @return a new sub-hyperplane, guaranteed to have no part outside
     * of the instance cell
     */
    private SubHyperplane<S> fitToCell(final SubHyperplane<S> sub) {
        SubHyperplane<S> s = sub;
        for (BSPTree<S> tree = this; tree.parent != null && s != null; tree = tree.parent) {
            if (tree == tree.parent.plus) {
                s = s.split(tree.parent.cut.getHyperplane()).getPlus();
            } else {
                s = s.split(tree.parent.cut.getHyperplane()).getMinus();
            }
        }
        return s;
    }

    /** Get the cell to which a point belongs.
     * <p>If the returned cell is a leaf node the points belongs to the
     * interior of the node, if the cell is an internal node the points
     * belongs to the node cut sub-hyperplane.</p>
     * @param point point to check
     * @return the tree cell to which the point belongs
     * @deprecated as of 3.3, replaced with {@link #getCell(Point, double)}
     */
    @Deprecated
    public BSPTree<S> getCell(final Vector<S> point) {
        return getCell((Point<S>) point, 1.0e-10);
    }

    /** Get the cell to which a point belongs.
     * <p>If the returned cell is a leaf node the points belongs to the
     * interior of the node, if the cell is an internal node the points
     * belongs to the node cut sub-hyperplane.</p>
     * @param point point to check
     * @param tolerance tolerance below which points close to a cut hyperplane
     * are considered to belong to the hyperplane itself
     * @return the tree cell to which the point belongs
     */
    public BSPTree<S> getCell(final Point<S> point, final double tolerance) {

        if (cut == null) {
            return this;
        }

        // position of the point with respect to the cut hyperplane
        final double offset = cut.getHyperplane().getOffset(point);

        if (FastMath.abs(offset) < tolerance) {
            return this;
        } else if (offset <= 0) {
            // point is on the minus side of the cut hyperplane
            return minus.getCell(point, tolerance);
        } else {
            // point is on the plus side of the cut hyperplane
            return plus.getCell(point, tolerance);
        }

    }

    /** Get the cells whose cut sub-hyperplanes are close to the point.
     * @param point point to check
     * @param maxOffset offset below which a cut sub-hyperplane is considered
     * close to the point (in absolute value)
     * @return close cells (may be empty if all cut sub-hyperplanes are farther
     * than maxOffset from the point)
     */
    public List<BSPTree<S>> getCloseCuts(final Point<S> point, final double maxOffset) {
        final List<BSPTree<S>> close = new ArrayList<BSPTree<S>>();
        recurseCloseCuts(point, maxOffset, close);
        return close;
    }

    /** Get the cells whose cut sub-hyperplanes are close to the point.
     * @param point point to check
     * @param maxOffset offset below which a cut sub-hyperplane is considered
     * close to the point (in absolute value)
     * @param close list to fill
     */
    private void recurseCloseCuts(final Point<S> point, final double maxOffset,
                                  final List<BSPTree<S>> close) {
        if (cut != null) {

            // position of the point with respect to the cut hyperplane
            final double offset = cut.getHyperplane().getOffset(point);

            if (offset < -maxOffset) {
                // point is on the minus side of the cut hyperplane
                minus.recurseCloseCuts(point, maxOffset, close);
            } else if (offset > maxOffset) {
                // point is on the plus side of the cut hyperplane
                plus.recurseCloseCuts(point, maxOffset, close);
            } else {
                // point is close to the cut hyperplane
                close.add(this);
                minus.recurseCloseCuts(point, maxOffset, close);
                plus.recurseCloseCuts(point, maxOffset, close);
            }

        }
    }

    /** Perform condensation on a tree.
     * <p>The condensation operation is not recursive, it must be called
     * explicitly from leaves to root.</p>
     */
    private void condense() {
        if ((cut != null) && (plus.cut == null) && (minus.cut == null) &&
            (((plus.attribute == null) && (minus.attribute == null)) ||
             ((plus.attribute != null) && plus.attribute.equals(minus.attribute)))) {
            attribute = (plus.attribute == null) ? minus.attribute : plus.attribute;
            cut       = null;
            plus      = null;
            minus     = null;
        }
    }

    /** Merge a BSP tree with the instance.
     * <p>All trees are modified (parts of them are reused in the new
     * tree), it is the responsibility of the caller to ensure a copy
     * has been done before if any of the former tree should be
     * preserved, <em>no</em> such copy is done here!</p>
     * <p>The algorithm used here is directly derived from the one
     * described in the Naylor, Amanatides and Thibault paper (section
     * III, Binary Partitioning of a BSP Tree).</p>
     * @param tree other tree to merge with the instance (will be
     * <em>unusable</em> after the operation, as well as the
     * instance itself)
     * @param leafMerger object implementing the final merging phase
     * (this is where the semantic of the operation occurs, generally
     * depending on the attribute of the leaf node)
     * @return a new tree, result of <code>instance &lt;op&gt;
     * tree</code>, this value can be ignored if parentTree is not null
     * since all connections have already been established
     */
    public BSPTree<S> merge(final BSPTree<S> tree, final LeafMerger<S> leafMerger) {
        return merge(tree, leafMerger, null, false);
    }

    /** Merge a BSP tree with the instance.
     * @param tree other tree to merge with the instance (will be
     * <em>unusable</em> after the operation, as well as the
     * instance itself)
     * @param leafMerger object implementing the final merging phase
     * (this is where the semantic of the operation occurs, generally
     * depending on the attribute of the leaf node)
     * @param parentTree parent tree to connect to (may be null)
     * @param isPlusChild if true and if parentTree is not null, the
     * resulting tree should be the plus child of its parent, ignored if
     * parentTree is null
     * @return a new tree, result of <code>instance &lt;op&gt;
     * tree</code>, this value can be ignored if parentTree is not null
     * since all connections have already been established
     */
    private BSPTree<S> merge(final BSPTree<S> tree, final LeafMerger<S> leafMerger,
                             final BSPTree<S> parentTree, final boolean isPlusChild) {
        if (cut == null) {
            // cell/tree operation
            return leafMerger.merge(this, tree, parentTree, isPlusChild, true);
        } else if (tree.cut == null) {
            // tree/cell operation
            return leafMerger.merge(tree, this, parentTree, isPlusChild, false);
        } else {
            // tree/tree operation
            final BSPTree<S> merged = tree.split(cut);
            if (parentTree != null) {
                merged.parent = parentTree;
                if (isPlusChild) {
                    parentTree.plus = merged;
                } else {
                    parentTree.minus = merged;
                }
            }

            // merging phase
            plus.merge(merged.plus, leafMerger, merged, true);
            minus.merge(merged.minus, leafMerger, merged, false);
            merged.condense();
            if (merged.cut != null) {
                merged.cut = merged.fitToCell(merged.cut.getHyperplane().wholeHyperplane());
            }

            return merged;

        }
    }

    /** This interface gather the merging operations between a BSP tree
     * leaf and another BSP tree.
     * <p>As explained in Bruce Naylor, John Amanatides and William
     * Thibault paper <a
     * href="http://www.cs.yorku.ca/~amana/research/bsptSetOp.pdf">Merging
     * BSP Trees Yields Polyhedral Set Operations</a>,
     * the operations on {@link BSPTree BSP trees} can be expressed as a
     * generic recursive merging operation where only the final part,
     * when one of the operand is a leaf, is specific to the real
     * operation semantics. For example, a tree representing a region
     * using a boolean attribute to identify inside cells and outside
     * cells would use four different objects to implement the final
     * merging phase of the four set operations union, intersection,
     * difference and symmetric difference (exclusive or).</p>
     * @param <S> Type of the space.
     */
    public interface LeafMerger<S extends Space> {

        /** Merge a leaf node and a tree node.
         * <p>This method is called at the end of a recursive merging
         * resulting from a {@code tree1.merge(tree2, leafMerger)}
         * call, when one of the sub-trees involved is a leaf (i.e. when
         * its cut-hyperplane is null). This is the only place where the
         * precise semantics of the operation are required. For all upper
         * level nodes in the tree, the merging operation is only a
         * generic partitioning algorithm.</p>
         * <p>Since the final operation may be non-commutative, it is
         * important to know if the leaf node comes from the instance tree
         * ({@code tree1}) or the argument tree
         * ({@code tree2}). The third argument of the method is
         * devoted to this. It can be ignored for commutative
         * operations.</p>
         * <p>The {@link BSPTree#insertInTree BSPTree.insertInTree} method
         * may be useful to implement this method.</p>
         * @param leaf leaf node (its cut hyperplane is guaranteed to be
         * null)
         * @param tree tree node (its cut hyperplane may be null or not)
         * @param parentTree parent tree to connect to (may be null)
         * @param isPlusChild if true and if parentTree is not null, the
         * resulting tree should be the plus child of its parent, ignored if
         * parentTree is null
         * @param leafFromInstance if true, the leaf node comes from the
         * instance tree ({@code tree1}) and the tree node comes from
         * the argument tree ({@code tree2})
         * @return the BSP tree resulting from the merging (may be one of
         * the arguments)
         */
        BSPTree<S> merge(BSPTree<S> leaf, BSPTree<S> tree, BSPTree<S> parentTree,
                         boolean isPlusChild, boolean leafFromInstance);

    }

    /** This interface handles the corner cases when an internal node cut sub-hyperplane vanishes.
     * <p>
     * Such cases happens for example when a cut sub-hyperplane is inserted into
     * another tree (during a merge operation), and is split in several parts,
     * some of which becomes smaller than the tolerance. The corresponding node
     * as then no cut sub-hyperplane anymore, but does have children. This interface
     * specifies how to handle this situation.
     * setting
     * </p>
     * @param <S> Type of the space.
     * @since 3.4
     */
    public interface VanishingCutHandler<S extends Space> {

        /** Fix a node with both vanished cut and children.
         * @param node node to fix
         * @return fixed node
         */
        BSPTree<S> fixNode(BSPTree<S> node);

    }

    /** Split a BSP tree by an external sub-hyperplane.
     * <p>Split a tree in two halves, on each side of the
     * sub-hyperplane. The instance is not modified.</p>
     * <p>The tree returned is not upward-consistent: despite all of its
     * sub-trees cut sub-hyperplanes (including its own cut
     * sub-hyperplane) are bounded to the current cell, it is <em>not</em>
     * attached to any parent tree yet. This tree is intended to be
     * later inserted into an higher level tree.</p>
     * <p>The algorithm used here is the one given in Naylor, Amanatides
     * and Thibault paper (section III, Binary Partitioning of a BSP
     * Tree).</p>
     * @param sub partitioning sub-hyperplane, must be already clipped
     * to the convex region represented by the instance, will be used as
     * the cut sub-hyperplane of the returned tree
     * @return a tree having the specified sub-hyperplane as its cut
     * sub-hyperplane, the two parts of the split instance as its two
     * sub-trees and a null parent
     */
    public BSPTree<S> split(final SubHyperplane<S> sub) {

        if (cut == null) {
            return new BSPTree<S>(sub, copySelf(), new BSPTree<S>(attribute), null);
        }

        final Hyperplane<S> cHyperplane = cut.getHyperplane();
        final Hyperplane<S> sHyperplane = sub.getHyperplane();
        final SubHyperplane.SplitSubHyperplane<S> subParts = sub.split(cHyperplane);
        switch (subParts.getSide()) {
        case PLUS :
        { // the partitioning sub-hyperplane is entirely in the plus sub-tree
            final BSPTree<S> split = plus.split(sub);
            if (cut.split(sHyperplane).getSide() == Side.PLUS) {
                split.plus =
                    new BSPTree<S>(cut.copySelf(), split.plus, minus.copySelf(), attribute);
                split.plus.condense();
                split.plus.parent = split;
            } else {
                split.minus =
                    new BSPTree<S>(cut.copySelf(), split.minus, minus.copySelf(), attribute);
                split.minus.condense();
                split.minus.parent = split;
            }
            return split;
        }
        case MINUS :
        { // the partitioning sub-hyperplane is entirely in the minus sub-tree
            final BSPTree<S> split = minus.split(sub);
            if (cut.split(sHyperplane).getSide() == Side.PLUS) {
                split.plus =
                    new BSPTree<S>(cut.copySelf(), plus.copySelf(), split.plus, attribute);
                split.plus.condense();
                split.plus.parent = split;
            } else {
                split.minus =
                    new BSPTree<S>(cut.copySelf(), plus.copySelf(), split.minus, attribute);
                split.minus.condense();
                split.minus.parent = split;
            }
            return split;
        }
        case BOTH :
        {
            final SubHyperplane.SplitSubHyperplane<S> cutParts = cut.split(sHyperplane);
            final BSPTree<S> split =
                new BSPTree<S>(sub, plus.split(subParts.getPlus()), minus.split(subParts.getMinus()),
                               null);
            split.plus.cut          = cutParts.getPlus();
            split.minus.cut         = cutParts.getMinus();
            final BSPTree<S> tmp    = split.plus.minus;
            split.plus.minus        = split.minus.plus;
            split.plus.minus.parent = split.plus;
            split.minus.plus        = tmp;
            split.minus.plus.parent = split.minus;
            split.plus.condense();
            split.minus.condense();
            return split;
        }
        default :
            return cHyperplane.sameOrientationAs(sHyperplane) ?
                   new BSPTree<S>(sub, plus.copySelf(),  minus.copySelf(), attribute) :
                   new BSPTree<S>(sub, minus.copySelf(), plus.copySelf(),  attribute);
        }

    }

    /** Insert the instance into another tree.
     * <p>The instance itself is modified so its former parent should
     * not be used anymore.</p>
     * @param parentTree parent tree to connect to (may be null)
     * @param isPlusChild if true and if parentTree is not null, the
     * resulting tree should be the plus child of its parent, ignored if
     * parentTree is null
     * @see LeafMerger
     * @deprecated as of 3.4, replaced with {@link #insertInTree(BSPTree, boolean, VanishingCutHandler)}
     */
    @Deprecated
    public void insertInTree(final BSPTree<S> parentTree, final boolean isPlusChild) {
        insertInTree(parentTree, isPlusChild, new VanishingCutHandler<S>() {
            /** {@inheritDoc} */
            public BSPTree<S> fixNode(BSPTree<S> node) {
                // the cut should not be null
                throw new MathIllegalStateException(LocalizedFormats.NULL_NOT_ALLOWED);
            }
        });
    }

    /** Insert the instance into another tree.
     * <p>The instance itself is modified so its former parent should
     * not be used anymore.</p>
     * @param parentTree parent tree to connect to (may be null)
     * @param isPlusChild if true and if parentTree is not null, the
     * resulting tree should be the plus child of its parent, ignored if
     * parentTree is null
     * @param vanishingHandler handler to use for handling very rare corner
     * cases of vanishing cut sub-hyperplanes in internal nodes during merging
     * @see LeafMerger
     * @since 3.4
     */
    public void insertInTree(final BSPTree<S> parentTree, final boolean isPlusChild,
                             final VanishingCutHandler<S> vanishingHandler) {

        // set up parent/child links
        parent = parentTree;
        if (parentTree != null) {
            if (isPlusChild) {
                parentTree.plus = this;
            } else {
                parentTree.minus = this;
            }
        }

        // make sure the inserted tree lies in the cell defined by its parent nodes
        if (cut != null) {

            // explore the parent nodes from here towards tree root
            for (BSPTree<S> tree = this; tree.parent != null; tree = tree.parent) {

                // this is an hyperplane of some parent node
                final Hyperplane<S> hyperplane = tree.parent.cut.getHyperplane();

                // chop off the parts of the inserted tree that extend
                // on the wrong side of this parent hyperplane
                if (tree == tree.parent.plus) {
                    cut = cut.split(hyperplane).getPlus();
                    plus.chopOffMinus(hyperplane, vanishingHandler);
                    minus.chopOffMinus(hyperplane, vanishingHandler);
                } else {
                    cut = cut.split(hyperplane).getMinus();
                    plus.chopOffPlus(hyperplane, vanishingHandler);
                    minus.chopOffPlus(hyperplane, vanishingHandler);
                }

                if (cut == null) {
                    // the cut sub-hyperplane has vanished
                    final BSPTree<S> fixed = vanishingHandler.fixNode(this);
                    cut       = fixed.cut;
                    plus      = fixed.plus;
                    minus     = fixed.minus;
                    attribute = fixed.attribute;
                    if (cut == null) {
                        break;
                    }
                }

            }

            // since we may have drop some parts of the inserted tree,
            // perform a condensation pass to keep the tree structure simple
            condense();

        }

    }

    /** Prune a tree around a cell.
     * <p>
     * This method can be used to extract a convex cell from a tree.
     * The original cell may either be a leaf node or an internal node.
     * If it is an internal node, it's subtree will be ignored (i.e. the
     * extracted cell will be a leaf node in all cases). The original
     * tree to which the original cell belongs is not touched at all,
     * a new independent tree will be built.
     * </p>
     * @param cellAttribute attribute to set for the leaf node
     * corresponding to the initial instance cell
     * @param otherLeafsAttributes attribute to set for the other leaf
     * nodes
     * @param internalAttributes attribute to set for the internal nodes
     * @return a new tree (the original tree is left untouched) containing
     * a single branch with the cell as a leaf node, and other leaf nodes
     * as the remnants of the pruned branches
     * @since 3.3
     */
    public BSPTree<S> pruneAroundConvexCell(final Object cellAttribute,
                                            final Object otherLeafsAttributes,
                                            final Object internalAttributes) {

        // build the current cell leaf
        BSPTree<S> tree = new BSPTree<S>(cellAttribute);

        // build the pruned tree bottom-up
        for (BSPTree<S> current = this; current.parent != null; current = current.parent) {
            final SubHyperplane<S> parentCut = current.parent.cut.copySelf();
            final BSPTree<S>       sibling   = new BSPTree<S>(otherLeafsAttributes);
            if (current == current.parent.plus) {
                tree = new BSPTree<S>(parentCut, tree, sibling, internalAttributes);
            } else {
                tree = new BSPTree<S>(parentCut, sibling, tree, internalAttributes);
            }
        }

        return tree;

    }

    /** Chop off parts of the tree.
     * <p>The instance is modified in place, all the parts that are on
     * the minus side of the chopping hyperplane are discarded, only the
     * parts on the plus side remain.</p>
     * @param hyperplane chopping hyperplane
     * @param vanishingHandler handler to use for handling very rare corner
     * cases of vanishing cut sub-hyperplanes in internal nodes during merging
     */
    private void chopOffMinus(final Hyperplane<S> hyperplane, final VanishingCutHandler<S> vanishingHandler) {
        if (cut != null) {

            cut = cut.split(hyperplane).getPlus();
            plus.chopOffMinus(hyperplane, vanishingHandler);
            minus.chopOffMinus(hyperplane, vanishingHandler);

            if (cut == null) {
                // the cut sub-hyperplane has vanished
                final BSPTree<S> fixed = vanishingHandler.fixNode(this);
                cut       = fixed.cut;
                plus      = fixed.plus;
                minus     = fixed.minus;
                attribute = fixed.attribute;
            }

        }
    }

    /** Chop off parts of the tree.
     * <p>The instance is modified in place, all the parts that are on
     * the plus side of the chopping hyperplane are discarded, only the
     * parts on the minus side remain.</p>
     * @param hyperplane chopping hyperplane
     * @param vanishingHandler handler to use for handling very rare corner
     * cases of vanishing cut sub-hyperplanes in internal nodes during merging
     */
    private void chopOffPlus(final Hyperplane<S> hyperplane, final VanishingCutHandler<S> vanishingHandler) {
        if (cut != null) {

            cut = cut.split(hyperplane).getMinus();
            plus.chopOffPlus(hyperplane, vanishingHandler);
            minus.chopOffPlus(hyperplane, vanishingHandler);

            if (cut == null) {
                // the cut sub-hyperplane has vanished
                final BSPTree<S> fixed = vanishingHandler.fixNode(this);
                cut       = fixed.cut;
                plus      = fixed.plus;
                minus     = fixed.minus;
                attribute = fixed.attribute;
            }

        }
    }

}
