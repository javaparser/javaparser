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
package org.apache.commons.collections4.list;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.lang.ref.WeakReference;
import java.util.ArrayList;
import java.util.Collection;
import java.util.ConcurrentModificationException;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;

/**
 * A <code>List</code> implementation with a <code>ListIterator</code> that
 * allows concurrent modifications to the underlying list.
 * <p>
 * This implementation supports all of the optional {@link List} operations.
 * It extends <code>AbstractLinkedList</code> and thus provides the
 * stack/queue/dequeue operations available in {@link java.util.LinkedList}.
 * <p>
 * The main feature of this class is the ability to modify the list and the
 * iterator at the same time. Both the {@link #listIterator()} and {@link #cursor()}
 * methods provides access to a <code>Cursor</code> instance which extends
 * <code>ListIterator</code>. The cursor allows changes to the list concurrent
 * with changes to the iterator. Note that the {@link #iterator()} method and
 * sublists do <b>not</b> provide this cursor behaviour.
 * <p>
 * The <code>Cursor</code> class is provided partly for backwards compatibility
 * and partly because it allows the cursor to be directly closed. Closing the
 * cursor is optional because references are held via a <code>WeakReference</code>.
 * For most purposes, simply modify the iterator and list at will, and then let
 * the garbage collector to the rest.
 * <p>
 * <b>Note that this implementation is not synchronized.</b>
 *
 * @see java.util.LinkedList
 * @since 1.0
 */
public class CursorableLinkedList<E> extends AbstractLinkedList<E> implements Serializable {

    /** Ensure serialization compatibility */
    private static final long serialVersionUID = 8836393098519411393L;

    /** A list of the cursor currently open on this list */
    private transient List<WeakReference<Cursor<E>>> cursors;

    //-----------------------------------------------------------------------
    /**
     * Constructor that creates.
     */
    public CursorableLinkedList() {
        super();
        init(); // must call init() as use super();
    }

    /**
     * Constructor that copies the specified collection
     *
     * @param coll  the collection to copy
     */
    public CursorableLinkedList(final Collection<? extends E> coll) {
        super(coll);
    }

    /**
     * The equivalent of a default constructor called
     * by any constructor and by <code>readObject</code>.
     */
    @Override
    protected void init() {
        super.init();
        cursors = new ArrayList<>();
    }

    //-----------------------------------------------------------------------
    /**
     * Returns an iterator that does <b>not</b> support concurrent modification.
     * <p>
     * If the underlying list is modified while iterating using this iterator
     * a ConcurrentModificationException will occur.
     * The cursor behaviour is available via {@link #listIterator()}.
     *
     * @return a new iterator that does <b>not</b> support concurrent modification
     */
    @Override
    public Iterator<E> iterator() {
        return super.listIterator(0);
    }

    /**
     * Returns a cursor iterator that allows changes to the underlying list in parallel.
     * <p>
     * The cursor enables iteration and list changes to occur in any order without
     * invalidating the iterator (from one thread). When elements are added to the
     * list, an event is fired to all active cursors enabling them to adjust to the
     * change in the list.
     * <p>
     * When the "current" (i.e., last returned by {@link ListIterator#next}
     * or {@link ListIterator#previous}) element of the list is removed,
     * the cursor automatically adjusts to the change (invalidating the
     * last returned value such that it cannot be removed).
     *
     * @return a new cursor iterator
     */
    @Override
    public ListIterator<E> listIterator() {
        return cursor(0);
    }

    /**
     * Returns a cursor iterator that allows changes to the underlying list in parallel.
     * <p>
     * The cursor enables iteration and list changes to occur in any order without
     * invalidating the iterator (from one thread). When elements are added to the
     * list, an event is fired to all active cursors enabling them to adjust to the
     * change in the list.
     * <p>
     * When the "current" (i.e., last returned by {@link ListIterator#next}
     * or {@link ListIterator#previous}) element of the list is removed,
     * the cursor automatically adjusts to the change (invalidating the
     * last returned value such that it cannot be removed).
     *
     * @param fromIndex  the index to start from
     * @return a new cursor iterator
     */
    @Override
    public ListIterator<E> listIterator(final int fromIndex) {
        return cursor(fromIndex);
    }

    /**
     * Returns a {@link Cursor} for iterating through the elements of this list.
     * <p>
     * A <code>Cursor</code> is a <code>ListIterator</code> with an additional
     * <code>close()</code> method. Calling this method immediately discards the
     * references to the cursor. If it is not called, then the garbage collector
     * will still remove the reference as it is held via a <code>WeakReference</code>.
     * <p>
     * The cursor enables iteration and list changes to occur in any order without
     * invalidating the iterator (from one thread). When elements are added to the
     * list, an event is fired to all active cursors enabling them to adjust to the
     * change in the list.
     * <p>
     * When the "current" (i.e., last returned by {@link ListIterator#next}
     * or {@link ListIterator#previous}) element of the list is removed,
     * the cursor automatically adjusts to the change (invalidating the
     * last returned value such that it cannot be removed).
     * <p>
     * The {@link #listIterator()} method returns the same as this method, and can
     * be cast to a <code>Cursor</code> if the <code>close</code> method is required.
     *
     * @return a new cursor iterator
     */
    public CursorableLinkedList.Cursor<E> cursor() {
        return cursor(0);
    }

    /**
     * Returns a {@link Cursor} for iterating through the elements of this list
     * starting from a specified index.
     * <p>
     * A <code>Cursor</code> is a <code>ListIterator</code> with an additional
     * <code>close()</code> method. Calling this method immediately discards the
     * references to the cursor. If it is not called, then the garbage collector
     * will still remove the reference as it is held via a <code>WeakReference</code>.
     * <p>
     * The cursor enables iteration and list changes to occur in any order without
     * invalidating the iterator (from one thread). When elements are added to the
     * list, an event is fired to all active cursors enabling them to adjust to the
     * change in the list.
     * <p>
     * When the "current" (i.e., last returned by {@link ListIterator#next}
     * or {@link ListIterator#previous}) element of the list is removed,
     * the cursor automatically adjusts to the change (invalidating the
     * last returned value such that it cannot be removed).
     * <p>
     * The {@link #listIterator(int)} method returns the same as this method, and can
     * be cast to a <code>Cursor</code> if the <code>close</code> method is required.
     *
     * @param fromIndex  the index to start from
     * @return a new cursor iterator
     * @throws IndexOutOfBoundsException if the index is out of range
     *      (index &lt; 0 || index &gt; size()).
     */
    public CursorableLinkedList.Cursor<E> cursor(final int fromIndex) {
        final Cursor<E> cursor = new Cursor<>(this, fromIndex);
        registerCursor(cursor);
        return cursor;
    }

    //-----------------------------------------------------------------------
    /**
     * Updates the node with a new value.
     * This implementation sets the value on the node.
     * Subclasses can override this to record the change.
     *
     * @param node  node to update
     * @param value  new value of the node
     */
    @Override
    protected void updateNode(final Node<E> node, final E value) {
        super.updateNode(node, value);
        broadcastNodeChanged(node);
    }

    /**
     * Inserts a new node into the list.
     *
     * @param nodeToInsert  new node to insert
     * @param insertBeforeNode  node to insert before
     * @throws NullPointerException if either node is null
     */
    @Override
    protected void addNode(final Node<E> nodeToInsert, final Node<E> insertBeforeNode) {
        super.addNode(nodeToInsert, insertBeforeNode);
        broadcastNodeInserted(nodeToInsert);
    }

    /**
     * Removes the specified node from the list.
     *
     * @param node  the node to remove
     * @throws NullPointerException if <code>node</code> is null
     */
    @Override
    protected void removeNode(final Node<E> node) {
        super.removeNode(node);
        broadcastNodeRemoved(node);
    }

    /**
     * Removes all nodes by iteration.
     */
    @Override
    protected void removeAllNodes() {
        if (size() > 0) {
            // superclass implementation would break all the iterators
            final Iterator<E> it = iterator();
            while (it.hasNext()) {
                it.next();
                it.remove();
            }
        }
    }

    //-----------------------------------------------------------------------
    /**
     * Registers a cursor to be notified of changes to this list.
     *
     * @param cursor  the cursor to register
     */
    protected void registerCursor(final Cursor<E> cursor) {
        // We take this opportunity to clean the cursors list
        // of WeakReference objects to garbage-collected cursors.
        for (final Iterator<WeakReference<Cursor<E>>> it = cursors.iterator(); it.hasNext();) {
            final WeakReference<Cursor<E>> ref = it.next();
            if (ref.get() == null) {
                it.remove();
            }
        }
        cursors.add(new WeakReference<>(cursor));
    }

    /**
     * Deregisters a cursor from the list to be notified of changes.
     *
     * @param cursor  the cursor to deregister
     */
    protected void unregisterCursor(final Cursor<E> cursor) {
        for (final Iterator<WeakReference<Cursor<E>>> it = cursors.iterator(); it.hasNext();) {
            final WeakReference<Cursor<E>> ref = it.next();
            final Cursor<E> cur = ref.get();
            if (cur == null) {
                // some other unrelated cursor object has been
                // garbage-collected; let's take the opportunity to
                // clean up the cursors list anyway..
                it.remove();
            } else if (cur == cursor) {
                ref.clear();
                it.remove();
                break;
            }
        }
    }

    //-----------------------------------------------------------------------
    /**
     * Informs all of my registered cursors that the specified
     * element was changed.
     *
     * @param node  the node that was changed
     */
    protected void broadcastNodeChanged(final Node<E> node) {
        final Iterator<WeakReference<Cursor<E>>> it = cursors.iterator();
        while (it.hasNext()) {
            final WeakReference<Cursor<E>> ref = it.next();
            final Cursor<E> cursor = ref.get();
            if (cursor == null) {
                it.remove(); // clean up list
            } else {
                cursor.nodeChanged(node);
            }
        }
    }

    /**
     * Informs all of my registered cursors that the specified
     * element was just removed from my list.
     *
     * @param node  the node that was changed
     */
    protected void broadcastNodeRemoved(final Node<E> node) {
        final Iterator<WeakReference<Cursor<E>>> it = cursors.iterator();
        while (it.hasNext()) {
            final WeakReference<Cursor<E>> ref = it.next();
            final Cursor<E> cursor = ref.get();
            if (cursor == null) {
                it.remove(); // clean up list
            } else {
                cursor.nodeRemoved(node);
            }
        }
    }

    /**
     * Informs all of my registered cursors that the specified
     * element was just added to my list.
     *
     * @param node  the node that was changed
     */
    protected void broadcastNodeInserted(final Node<E> node) {
        final Iterator<WeakReference<Cursor<E>>> it = cursors.iterator();
        while (it.hasNext()) {
            final WeakReference<Cursor<E>> ref = it.next();
            final Cursor<E> cursor = ref.get();
            if (cursor == null) {
                it.remove(); // clean up list
            } else {
                cursor.nodeInserted(node);
            }
        }
    }

    //-----------------------------------------------------------------------
    /**
     * Serializes the data held in this object to the stream specified.
     *
     * @param out  the output stream
     * @throws IOException if an error occurs while writing to the stream
     */
    private void writeObject(final ObjectOutputStream out) throws IOException {
        out.defaultWriteObject();
        doWriteObject(out);
    }

    /**
     * Deserializes the data held in this object to the stream specified.
     *
     * @param in  the input stream
     * @throws IOException if an error occurs while reading from the stream
     * @throws ClassNotFoundException if an object read from the stream can not be loaded
     */
    private void readObject(final ObjectInputStream in) throws IOException, ClassNotFoundException {
        in.defaultReadObject();
        doReadObject(in);
    }

    //-----------------------------------------------------------------------
    /**
     * Creates a list iterator for the sublist.
     *
     * @param subList  the sublist to get an iterator for
     * @param fromIndex  the index to start from, relative to the sublist
     * @return the list iterator for the sublist
     */
    @Override
    protected ListIterator<E> createSubListListIterator(final LinkedSubList<E> subList, final int fromIndex) {
        final SubCursor<E> cursor = new SubCursor<>(subList, fromIndex);
        registerCursor(cursor);
        return cursor;
    }

    //-----------------------------------------------------------------------
    /**
     * An extended <code>ListIterator</code> that allows concurrent changes to
     * the underlying list.
     */
    public static class Cursor<E> extends AbstractLinkedList.LinkedListIterator<E> {
        /** Is the cursor valid (not closed) */
        boolean valid = true;
        /** Is the next index valid */
        boolean nextIndexValid = true;
        /** Flag to indicate if the current element was removed by another object. */
        boolean currentRemovedByAnother = false;

        /**
         * Constructs a new cursor.
         *
         * @param parent  the parent list
         * @param index  the index to start from
         */
        protected Cursor(final CursorableLinkedList<E> parent, final int index) {
            super(parent, index);
            valid = true;
        }

        /**
         * Removes the item last returned by this iterator.
         * <p>
         * There may have been subsequent alterations to the list
         * since you obtained this item, however you can still remove it.
         * You can even remove it if the item is no longer in the main list.
         * However, you can't call this method on the same iterator more
         * than once without calling next() or previous().
         *
         * @throws IllegalStateException if there is no item to remove
         */
        @Override
        public void remove() {
            // overridden, as the nodeRemoved() method updates the iterator
            // state in the parent.removeNode() call below
            if (current == null && currentRemovedByAnother) { // NOPMD
                // quietly ignore, as the last returned node was removed
                // by the list or some other iterator
                // by ignoring it, we keep this iterator independent from
                // other changes as much as possible
            } else {
                checkModCount();
                parent.removeNode(getLastNodeReturned());
            }
            currentRemovedByAnother = false;
        }

        /**
         * Adds an object to the list.
         * The object added here will be the new 'previous' in the iterator.
         *
         * @param obj  the object to add
         */
        @Override
        public void add(final E obj) {
            // overridden, as the nodeInserted() method updates the iterator state
            super.add(obj);
            // matches the (next.previous == node) clause in nodeInserted()
            // thus next gets changed - reset it again here
            next = next.next;
        }

        // set is not overridden, as it works ok
        // note that we want it to throw an exception if the element being
        // set has been removed from the real list (compare this with the
        // remove method where we silently ignore this case)

        /**
         * Gets the index of the next element to be returned.
         *
         * @return the next index
         */
        @Override
        public int nextIndex() {
            if (nextIndexValid == false) {
                if (next == parent.header) {
                    nextIndex = parent.size();
                } else {
                    int pos = 0;
                    Node<E> temp = parent.header.next;
                    while (temp != next) {
                        pos++;
                        temp = temp.next;
                    }
                    nextIndex = pos;
                }
                nextIndexValid = true;
            }
            return nextIndex;
        }

        /**
         * Handle event from the list when a node has changed.
         *
         * @param node  the node that changed
         */
        protected void nodeChanged(final Node<E> node) {
            // do nothing
        }

        /**
         * Handle event from the list when a node has been removed.
         *
         * @param node  the node that was removed
         */
        protected void nodeRemoved(final Node<E> node) {
            if (node == next && node == current) {
                // state where next() followed by previous()
                next = node.next;
                current = null;
                currentRemovedByAnother = true;
            } else if (node == next) {
                // state where next() not followed by previous()
                // and we are matching next node
                next = node.next;
                currentRemovedByAnother = false;
            } else if (node == current) {
                // state where next() not followed by previous()
                // and we are matching current (last returned) node
                current = null;
                currentRemovedByAnother = true;
                nextIndex--;
            } else {
                nextIndexValid = false;
                currentRemovedByAnother = false;
            }
        }

        /**
         * Handle event from the list when a node has been added.
         *
         * @param node  the node that was added
         */
        protected void nodeInserted(final Node<E> node) {
            if (node.previous == current) {
                next = node;
            } else if (next.previous == node) {
                next = node;
            } else {
                nextIndexValid = false;
            }
        }

        /**
         * Override superclass modCount check, and replace it with our valid flag.
         */
        @Override
        protected void checkModCount() {
            if (!valid) {
                throw new ConcurrentModificationException("Cursor closed");
            }
        }

        /**
         * Mark this cursor as no longer being needed. Any resources
         * associated with this cursor are immediately released.
         * In previous versions of this class, it was mandatory to close
         * all cursor objects to avoid memory leaks. It is <i>no longer</i>
         * necessary to call this close method; an instance of this class
         * can now be treated exactly like a normal iterator.
         */
        public void close() {
            if (valid) {
                ((CursorableLinkedList<E>) parent).unregisterCursor(this);
                valid = false;
            }
        }
    }

    //-----------------------------------------------------------------------
    /**
     * A cursor for the sublist based on LinkedSubListIterator.
     *
     * @since 3.2
     */
    protected static class SubCursor<E> extends Cursor<E> {

        /** The parent list */
        protected final LinkedSubList<E> sub;

        /**
         * Constructs a new cursor.
         *
         * @param sub  the sub list
         * @param index  the index to start from
         */
        protected SubCursor(final LinkedSubList<E> sub, final int index) {
            super((CursorableLinkedList<E>) sub.parent, index + sub.offset);
            this.sub = sub;
        }

        @Override
        public boolean hasNext() {
            return nextIndex() < sub.size;
        }

        @Override
        public boolean hasPrevious() {
            return previousIndex() >= 0;
        }

        @Override
        public int nextIndex() {
            return super.nextIndex() - sub.offset;
        }

        @Override
        public void add(final E obj) {
            super.add(obj);
            sub.expectedModCount = parent.modCount;
            sub.size++;
        }

        @Override
        public void remove() {
            super.remove();
            sub.expectedModCount = parent.modCount;
            sub.size--;
        }
    }

}
