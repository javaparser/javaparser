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
package org.apache.commons.math3.geometry.partitioning.utilities;

/** This class implements AVL trees.
 *
 * <p>The purpose of this class is to sort elements while allowing
 * duplicate elements (i.e. such that {@code a.equals(b)} is
 * true). The {@code SortedSet} interface does not allow this, so
 * a specific class is needed. Null elements are not allowed.</p>
 *
 * <p>Since the {@code equals} method is not sufficient to
 * differentiate elements, the {@link #delete delete} method is
 * implemented using the equality operator.</p>
 *
 * <p>In order to clearly mark the methods provided here do not have
 * the same semantics as the ones specified in the
 * {@code SortedSet} interface, different names are used
 * ({@code add} has been replaced by {@link #insert insert} and
 * {@code remove} has been replaced by {@link #delete
 * delete}).</p>
 *
 * <p>This class is based on the C implementation Georg Kraml has put
 * in the public domain. Unfortunately, his <a
 * href="www.purists.org/georg/avltree/index.html">page</a> seems not
 * to exist any more.</p>
 *
 * @param <T> the type of the elements
 *
 * @since 3.0
 * @deprecated as of 3.4, this class is not used anymore and considered
 * to be out of scope of Apache Commons Math
 */
@Deprecated
public class AVLTree<T extends Comparable<T>> {

    /** Top level node. */
    private Node top;

    /** Build an empty tree.
     */
    public AVLTree() {
        top = null;
    }

    /** Insert an element in the tree.
     * @param element element to insert (silently ignored if null)
     */
    public void insert(final T element) {
        if (element != null) {
            if (top == null) {
                top = new Node(element, null);
            } else {
                top.insert(element);
            }
        }
    }

    /** Delete an element from the tree.
     * <p>The element is deleted only if there is a node {@code n}
     * containing exactly the element instance specified, i.e. for which
     * {@code n.getElement() == element}. This is purposely
     * <em>different</em> from the specification of the
     * {@code java.util.Set} {@code remove} method (in fact,
     * this is the reason why a specific class has been developed).</p>
     * @param element element to delete (silently ignored if null)
     * @return true if the element was deleted from the tree
     */
    public boolean delete(final T element) {
        if (element != null) {
            for (Node node = getNotSmaller(element); node != null; node = node.getNext()) {
                // loop over all elements neither smaller nor larger
                // than the specified one
                if (node.element == element) {
                    node.delete();
                    return true;
                } else if (node.element.compareTo(element) > 0) {
                    // all the remaining elements are known to be larger,
                    // the element is not in the tree
                    return false;
                }
            }
        }
        return false;
    }

    /** Check if the tree is empty.
     * @return true if the tree is empty
     */
    public boolean isEmpty() {
        return top == null;
    }


    /** Get the number of elements of the tree.
     * @return number of elements contained in the tree
     */
    public int size() {
        return (top == null) ? 0 : top.size();
    }

    /** Get the node whose element is the smallest one in the tree.
     * @return the tree node containing the smallest element in the tree
     * or null if the tree is empty
     * @see #getLargest
     * @see #getNotSmaller
     * @see #getNotLarger
     * @see Node#getPrevious
     * @see Node#getNext
     */
    public Node getSmallest() {
        return (top == null) ? null : top.getSmallest();
    }

    /** Get the node whose element is the largest one in the tree.
     * @return the tree node containing the largest element in the tree
     * or null if the tree is empty
     * @see #getSmallest
     * @see #getNotSmaller
     * @see #getNotLarger
     * @see Node#getPrevious
     * @see Node#getNext
     */
    public Node getLargest() {
        return (top == null) ? null : top.getLargest();
    }

    /** Get the node whose element is not smaller than the reference object.
     * @param reference reference object (may not be in the tree)
     * @return the tree node containing the smallest element not smaller
     * than the reference object or null if either the tree is empty or
     * all its elements are smaller than the reference object
     * @see #getSmallest
     * @see #getLargest
     * @see #getNotLarger
     * @see Node#getPrevious
     * @see Node#getNext
     */
    public Node getNotSmaller(final T reference) {
        Node candidate = null;
        for (Node node = top; node != null;) {
            if (node.element.compareTo(reference) < 0) {
                if (node.right == null) {
                    return candidate;
                }
                node = node.right;
            } else {
                candidate = node;
                if (node.left == null) {
                    return candidate;
                }
                node = node.left;
            }
        }
        return null;
    }

    /** Get the node whose element is not larger than the reference object.
     * @param reference reference object (may not be in the tree)
     * @return the tree node containing the largest element not larger
     * than the reference object (in which case the node is guaranteed
     * not to be empty) or null if either the tree is empty or all its
     * elements are larger than the reference object
     * @see #getSmallest
     * @see #getLargest
     * @see #getNotSmaller
     * @see Node#getPrevious
     * @see Node#getNext
     */
    public Node getNotLarger(final T reference) {
        Node candidate = null;
        for (Node node = top; node != null;) {
            if (node.element.compareTo(reference) > 0) {
                if (node.left == null) {
                    return candidate;
                }
                node = node.left;
            } else {
                candidate = node;
                if (node.right == null) {
                    return candidate;
                }
                node = node.right;
            }
        }
        return null;
    }

    /** Enum for tree skew factor. */
    private enum Skew {
        /** Code for left high trees. */
        LEFT_HIGH,

        /** Code for right high trees. */
        RIGHT_HIGH,

        /** Code for Skew.BALANCED trees. */
        BALANCED;
    }

    /** This class implements AVL trees nodes.
     * <p>AVL tree nodes implement all the logical structure of the
     * tree. Nodes are created by the {@link AVLTree AVLTree} class.</p>
     * <p>The nodes are not independant from each other but must obey
     * specific balancing constraints and the tree structure is
     * rearranged as elements are inserted or deleted from the tree. The
     * creation, modification and tree-related navigation methods have
     * therefore restricted access. Only the order-related navigation,
     * reading and delete methods are public.</p>
     * @see AVLTree
     */
    public class Node {

        /** Element contained in the current node. */
        private T element;

        /** Left sub-tree. */
        private Node left;

        /** Right sub-tree. */
        private Node right;

        /** Parent tree. */
        private Node parent;

        /** Skew factor. */
        private Skew skew;

        /** Build a node for a specified element.
         * @param element element
         * @param parent parent node
         */
        Node(final T element, final Node parent) {
            this.element = element;
            left         = null;
            right        = null;
            this.parent  = parent;
            skew         = Skew.BALANCED;
        }

        /** Get the contained element.
         * @return element contained in the node
         */
        public T getElement() {
            return element;
        }

        /** Get the number of elements of the tree rooted at this node.
         * @return number of elements contained in the tree rooted at this node
         */
        int size() {
            return 1 + ((left  == null) ? 0 : left.size()) + ((right == null) ? 0 : right.size());
        }

        /** Get the node whose element is the smallest one in the tree
         * rooted at this node.
         * @return the tree node containing the smallest element in the
         * tree rooted at this node or null if the tree is empty
         * @see #getLargest
         */
        Node getSmallest() {
            Node node = this;
            while (node.left != null) {
                node = node.left;
            }
            return node;
        }

        /** Get the node whose element is the largest one in the tree
         * rooted at this node.
         * @return the tree node containing the largest element in the
         * tree rooted at this node or null if the tree is empty
         * @see #getSmallest
         */
        Node getLargest() {
            Node node = this;
            while (node.right != null) {
                node = node.right;
            }
            return node;
        }

        /** Get the node containing the next smaller or equal element.
         * @return node containing the next smaller or equal element or
         * null if there is no smaller or equal element in the tree
         * @see #getNext
         */
        public Node getPrevious() {

            if (left != null) {
                final Node node = left.getLargest();
                if (node != null) {
                    return node;
                }
            }

            for (Node node = this; node.parent != null; node = node.parent) {
                if (node != node.parent.left) {
                    return node.parent;
                }
            }

            return null;

        }

        /** Get the node containing the next larger or equal element.
         * @return node containing the next larger or equal element (in
         * which case the node is guaranteed not to be empty) or null if
         * there is no larger or equal element in the tree
         * @see #getPrevious
         */
        public Node getNext() {

            if (right != null) {
                final Node node = right.getSmallest();
                if (node != null) {
                    return node;
                }
            }

            for (Node node = this; node.parent != null; node = node.parent) {
                if (node != node.parent.right) {
                    return node.parent;
                }
            }

            return null;

        }

        /** Insert an element in a sub-tree.
         * @param newElement element to insert
         * @return true if the parent tree should be re-Skew.BALANCED
         */
        boolean insert(final T newElement) {
            if (newElement.compareTo(this.element) < 0) {
                // the inserted element is smaller than the node
                if (left == null) {
                    left = new Node(newElement, this);
                    return rebalanceLeftGrown();
                }
                return left.insert(newElement) ? rebalanceLeftGrown() : false;
            }

            // the inserted element is equal to or greater than the node
            if (right == null) {
                right = new Node(newElement, this);
                return rebalanceRightGrown();
            }
            return right.insert(newElement) ? rebalanceRightGrown() : false;

        }

        /** Delete the node from the tree.
         */
        public void delete() {
            if ((parent == null) && (left == null) && (right == null)) {
                // this was the last node, the tree is now empty
                element = null;
                top     = null;
            } else {

                Node node;
                Node child;
                boolean leftShrunk;
                if ((left == null) && (right == null)) {
                    node       = this;
                    element    = null;
                    leftShrunk = node == node.parent.left;
                    child      = null;
                } else {
                    node       = (left != null) ? left.getLargest() : right.getSmallest();
                    element    = node.element;
                    leftShrunk = node == node.parent.left;
                    child      = (node.left != null) ? node.left : node.right;
                }

                node = node.parent;
                if (leftShrunk) {
                    node.left = child;
                } else {
                    node.right = child;
                }
                if (child != null) {
                    child.parent = node;
                }

                while (leftShrunk ? node.rebalanceLeftShrunk() : node.rebalanceRightShrunk()) {
                    if (node.parent == null) {
                        return;
                    }
                    leftShrunk = node == node.parent.left;
                    node = node.parent;
                }

            }
        }

        /** Re-balance the instance as left sub-tree has grown.
         * @return true if the parent tree should be reSkew.BALANCED too
         */
        private boolean rebalanceLeftGrown() {
            switch (skew) {
            case LEFT_HIGH:
                if (left.skew == Skew.LEFT_HIGH) {
                    rotateCW();
                    skew       = Skew.BALANCED;
                    right.skew = Skew.BALANCED;
                } else {
                    final Skew s = left.right.skew;
                    left.rotateCCW();
                    rotateCW();
                    switch(s) {
                    case LEFT_HIGH:
                        left.skew  = Skew.BALANCED;
                        right.skew = Skew.RIGHT_HIGH;
                        break;
                    case RIGHT_HIGH:
                        left.skew  = Skew.LEFT_HIGH;
                        right.skew = Skew.BALANCED;
                        break;
                    default:
                        left.skew  = Skew.BALANCED;
                        right.skew = Skew.BALANCED;
                    }
                    skew = Skew.BALANCED;
                }
                return false;
            case RIGHT_HIGH:
                skew = Skew.BALANCED;
                return false;
            default:
                skew = Skew.LEFT_HIGH;
                return true;
            }
        }

        /** Re-balance the instance as right sub-tree has grown.
         * @return true if the parent tree should be reSkew.BALANCED too
         */
        private boolean rebalanceRightGrown() {
            switch (skew) {
            case LEFT_HIGH:
                skew = Skew.BALANCED;
                return false;
            case RIGHT_HIGH:
                if (right.skew == Skew.RIGHT_HIGH) {
                    rotateCCW();
                    skew      = Skew.BALANCED;
                    left.skew = Skew.BALANCED;
                } else {
                    final Skew s = right.left.skew;
                    right.rotateCW();
                    rotateCCW();
                    switch (s) {
                    case LEFT_HIGH:
                        left.skew  = Skew.BALANCED;
                        right.skew = Skew.RIGHT_HIGH;
                        break;
                    case RIGHT_HIGH:
                        left.skew  = Skew.LEFT_HIGH;
                        right.skew = Skew.BALANCED;
                        break;
                    default:
                        left.skew  = Skew.BALANCED;
                        right.skew = Skew.BALANCED;
                    }
                    skew = Skew.BALANCED;
                }
                return false;
            default:
                skew = Skew.RIGHT_HIGH;
                return true;
            }
        }

        /** Re-balance the instance as left sub-tree has shrunk.
         * @return true if the parent tree should be reSkew.BALANCED too
         */
        private boolean rebalanceLeftShrunk() {
            switch (skew) {
            case LEFT_HIGH:
                skew = Skew.BALANCED;
                return true;
            case RIGHT_HIGH:
                if (right.skew == Skew.RIGHT_HIGH) {
                    rotateCCW();
                    skew      = Skew.BALANCED;
                    left.skew = Skew.BALANCED;
                    return true;
                } else if (right.skew == Skew.BALANCED) {
                    rotateCCW();
                    skew      = Skew.LEFT_HIGH;
                    left.skew = Skew.RIGHT_HIGH;
                    return false;
                } else {
                    final Skew s = right.left.skew;
                    right.rotateCW();
                    rotateCCW();
                    switch (s) {
                    case LEFT_HIGH:
                        left.skew  = Skew.BALANCED;
                        right.skew = Skew.RIGHT_HIGH;
                        break;
                    case RIGHT_HIGH:
                        left.skew  = Skew.LEFT_HIGH;
                        right.skew = Skew.BALANCED;
                        break;
                    default:
                        left.skew  = Skew.BALANCED;
                        right.skew = Skew.BALANCED;
                    }
                    skew = Skew.BALANCED;
                    return true;
                }
            default:
                skew = Skew.RIGHT_HIGH;
                return false;
            }
        }

        /** Re-balance the instance as right sub-tree has shrunk.
         * @return true if the parent tree should be reSkew.BALANCED too
         */
        private boolean rebalanceRightShrunk() {
            switch (skew) {
            case RIGHT_HIGH:
                skew = Skew.BALANCED;
                return true;
            case LEFT_HIGH:
                if (left.skew == Skew.LEFT_HIGH) {
                    rotateCW();
                    skew       = Skew.BALANCED;
                    right.skew = Skew.BALANCED;
                    return true;
                } else if (left.skew == Skew.BALANCED) {
                    rotateCW();
                    skew       = Skew.RIGHT_HIGH;
                    right.skew = Skew.LEFT_HIGH;
                    return false;
                } else {
                    final Skew s = left.right.skew;
                    left.rotateCCW();
                    rotateCW();
                    switch (s) {
                    case LEFT_HIGH:
                        left.skew  = Skew.BALANCED;
                        right.skew = Skew.RIGHT_HIGH;
                        break;
                    case RIGHT_HIGH:
                        left.skew  = Skew.LEFT_HIGH;
                        right.skew = Skew.BALANCED;
                        break;
                    default:
                        left.skew  = Skew.BALANCED;
                        right.skew = Skew.BALANCED;
                    }
                    skew = Skew.BALANCED;
                    return true;
                }
            default:
                skew = Skew.LEFT_HIGH;
                return false;
            }
        }

        /** Perform a clockwise rotation rooted at the instance.
         * <p>The skew factor are not updated by this method, they
         * <em>must</em> be updated by the caller</p>
         */
        private void rotateCW() {

            final T tmpElt       = element;
            element              = left.element;
            left.element         = tmpElt;

            final Node tmpNode   = left;
            left                 = tmpNode.left;
            tmpNode.left         = tmpNode.right;
            tmpNode.right        = right;
            right                = tmpNode;

            if (left != null) {
                left.parent = this;
            }
            if (right.right != null) {
                right.right.parent = right;
            }

        }

        /** Perform a counter-clockwise rotation rooted at the instance.
         * <p>The skew factor are not updated by this method, they
         * <em>must</em> be updated by the caller</p>
         */
        private void rotateCCW() {

            final T tmpElt        = element;
            element               = right.element;
            right.element         = tmpElt;

            final Node tmpNode    = right;
            right                 = tmpNode.right;
            tmpNode.right         = tmpNode.left;
            tmpNode.left          = left;
            left                  = tmpNode;

            if (right != null) {
                right.parent = this;
            }
            if (left.left != null) {
                left.left.parent = left;
            }

        }

    }

}
