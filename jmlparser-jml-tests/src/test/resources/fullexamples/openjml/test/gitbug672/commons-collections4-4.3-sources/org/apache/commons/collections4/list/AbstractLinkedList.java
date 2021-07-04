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
import java.lang.reflect.Array;
import java.util.AbstractList;
import java.util.Collection;
import java.util.ConcurrentModificationException;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
import java.util.NoSuchElementException;

import org.apache.commons.collections4.OrderedIterator;

/**
 * An abstract implementation of a linked list which provides numerous points for
 * subclasses to override.
 * <p>
 * Overridable methods are provided to change the storage node and to change how
 * nodes are added to and removed. Hopefully, all you need for unusual subclasses
 * is here.
 *
 * @since 3.0
 */
public abstract class AbstractLinkedList<E> implements List<E> {

    /*
     * Implementation notes:
     * - a standard circular doubly-linked list
     * - a marker node is stored to mark the start and the end of the list
     * - node creation and removal always occurs through createNode() and
     *   removeNode().
     * - a modification count is kept, with the same semantics as
     * {@link java.util.LinkedList}.
     * - respects {@link AbstractList#modCount}
     */

    /**
     * A {@link Node} which indicates the start and end of the list and does not
     * hold a value. The value of <code>next</code> is the first item in the
     * list. The value of of <code>previous</code> is the last item in the list.
     */
    transient Node<E> header;

    /** The size of the list */
    transient int size;

    /** Modification count for iterators */
    transient int modCount;

    /**
     * Constructor that does nothing intended for deserialization.
     * <p>
     * If this constructor is used by a serializable subclass then the init()
     * method must be called.
     */
    protected AbstractLinkedList() {
        super();
    }

    /**
     * Constructs a list copying data from the specified collection.
     *
     * @param coll  the collection to copy
     */
    protected AbstractLinkedList(final Collection<? extends E> coll) {
        super();
        init();
        addAll(coll);
    }

    /**
     * The equivalent of a default constructor, broken out so it can be called
     * by any constructor and by <code>readObject</code>.
     * Subclasses which override this method should make sure they call super,
     * so the list is initialised properly.
     */
    protected void init() {
        header = createHeaderNode();
    }

    //-----------------------------------------------------------------------

    @Override
    public int size() {
        return size;
    }

    @Override
    public boolean isEmpty() {
        return size() == 0;
    }

    @Override
    public E get(final int index) {
        final Node<E> node = getNode(index, false);
        return node.getValue();
    }

    //-----------------------------------------------------------------------

    @Override
    public Iterator<E> iterator() {
        return listIterator();
    }

    @Override
    public ListIterator<E> listIterator() {
        return new LinkedListIterator<>(this, 0);
    }

    @Override
    public ListIterator<E> listIterator(final int fromIndex) {
        return new LinkedListIterator<>(this, fromIndex);
    }

    //-----------------------------------------------------------------------

    @Override
    public int indexOf(final Object value) {
        int i = 0;
        for (Node<E> node = header.next; node != header; node = node.next) {
            if (isEqualValue(node.getValue(), value)) {
                return i;
            }
            i++;
        }
        return -1;
    }

    @Override
    public int lastIndexOf(final Object value) {
        int i = size - 1;
        for (Node<E> node = header.previous; node != header; node = node.previous) {
            if (isEqualValue(node.getValue(), value)) {
                return i;
            }
            i--;
        }
        return -1;
    }

    @Override
    public boolean contains(final Object value) {
        return indexOf(value) != -1;
    }

    @Override
    public boolean containsAll(final Collection<?> coll) {
        for (final Object o : coll) {
            if (!contains(o)) {
                return false;
            }
        }
        return true;
    }

    //-----------------------------------------------------------------------

    @Override
    public Object[] toArray() {
        return toArray(new Object[size]);
    }

    @Override
    @SuppressWarnings("unchecked")
    public <T> T[] toArray(T[] array) {
        // Extend the array if needed
        if (array.length < size) {
            final Class<?> componentType = array.getClass().getComponentType();
            array = (T[]) Array.newInstance(componentType, size);
        }
        // Copy the values into the array
        int i = 0;
        for (Node<E> node = header.next; node != header; node = node.next, i++) {
            array[i] = (T) node.getValue();
        }
        // Set the value after the last value to null
        if (array.length > size) {
            array[size] = null;
        }
        return array;
    }

    /**
     * Gets a sublist of the main list.
     *
     * @param fromIndexInclusive  the index to start from
     * @param toIndexExclusive  the index to end at
     * @return the new sublist
     */
    @Override
    public List<E> subList(final int fromIndexInclusive, final int toIndexExclusive) {
        return new LinkedSubList<>(this, fromIndexInclusive, toIndexExclusive);
    }

    //-----------------------------------------------------------------------

    @Override
    public boolean add(final E value) {
        addLast(value);
        return true;
    }

    @Override
    public void add(final int index, final E value) {
        final Node<E> node = getNode(index, true);
        addNodeBefore(node, value);
    }

    @Override
    public boolean addAll(final Collection<? extends E> coll) {
        return addAll(size, coll);
    }

    @Override
    public boolean addAll(final int index, final Collection<? extends E> coll) {
        final Node<E> node = getNode(index, true);
        for (final E e : coll) {
            addNodeBefore(node, e);
        }
        return true;
    }

    //-----------------------------------------------------------------------

    @Override
    public E remove(final int index) {
        final Node<E> node = getNode(index, false);
        final E oldValue = node.getValue();
        removeNode(node);
        return oldValue;
    }

    @Override
    public boolean remove(final Object value) {
        for (Node<E> node = header.next; node != header; node = node.next) {
            if (isEqualValue(node.getValue(), value)) {
                removeNode(node);
                return true;
            }
        }
        return false;
    }

    /**
     * {@inheritDoc}
     * <p>
     * This implementation iterates over the elements of this list, checking each element in
     * turn to see if it's contained in <code>coll</code>. If it's contained, it's removed
     * from this list. As a consequence, it is advised to use a collection type for
     * <code>coll</code> that provides a fast (e.g. O(1)) implementation of
     * {@link Collection#contains(Object)}.
     */
    @Override
    public boolean removeAll(final Collection<?> coll) {
        boolean modified = false;
        final Iterator<E> it = iterator();
        while (it.hasNext()) {
            if (coll.contains(it.next())) {
                it.remove();
                modified = true;
            }
        }
        return modified;
    }

    //-----------------------------------------------------------------------

    /**
     * {@inheritDoc}
     * <p>
     * This implementation iterates over the elements of this list, checking each element in
     * turn to see if it's contained in <code>coll</code>. If it's not contained, it's removed
     * from this list. As a consequence, it is advised to use a collection type for
     * <code>coll</code> that provides a fast (e.g. O(1)) implementation of
     * {@link Collection#contains(Object)}.
     */
    @Override
    public boolean retainAll(final Collection<?> coll) {
        boolean modified = false;
        final Iterator<E> it = iterator();
        while (it.hasNext()) {
            if (coll.contains(it.next()) == false) {
                it.remove();
                modified = true;
            }
        }
        return modified;
    }

    @Override
    public E set(final int index, final E value) {
        final Node<E> node = getNode(index, false);
        final E oldValue = node.getValue();
        updateNode(node, value);
        return oldValue;
    }

    @Override
    public void clear() {
        removeAllNodes();
    }

    //-----------------------------------------------------------------------

    public E getFirst() {
        final Node<E> node = header.next;
        if (node == header) {
            throw new NoSuchElementException();
        }
        return node.getValue();
    }

    public E getLast() {
        final Node<E> node = header.previous;
        if (node == header) {
            throw new NoSuchElementException();
        }
        return node.getValue();
    }

    public boolean addFirst(final E o) {
        addNodeAfter(header, o);
        return true;
    }

    public boolean addLast(final E o) {
        addNodeBefore(header, o);
        return true;
    }

    public E removeFirst() {
        final Node<E> node = header.next;
        if (node == header) {
            throw new NoSuchElementException();
        }
        final E oldValue = node.getValue();
        removeNode(node);
        return oldValue;
    }

    public E removeLast() {
        final Node<E> node = header.previous;
        if (node == header) {
            throw new NoSuchElementException();
        }
        final E oldValue = node.getValue();
        removeNode(node);
        return oldValue;
    }

    //-----------------------------------------------------------------------
    @Override
    public boolean equals(final Object obj) {
        if (obj == this) {
            return true;
        }
        if (obj instanceof List == false) {
            return false;
        }
        final List<?> other = (List<?>) obj;
        if (other.size() != size()) {
            return false;
        }
        final ListIterator<?> it1 = listIterator();
        final ListIterator<?> it2 = other.listIterator();
        while (it1.hasNext() && it2.hasNext()) {
            final Object o1 = it1.next();
            final Object o2 = it2.next();
            if (!(o1 == null ? o2 == null : o1.equals(o2))) {
                return false;
            }
        }
        return !(it1.hasNext() || it2.hasNext());
    }

    @Override
    public int hashCode() {
        int hashCode = 1;
        for (final E e : this) {
            hashCode = 31 * hashCode + (e == null ? 0 : e.hashCode());
        }
        return hashCode;
    }

    @Override
    public String toString() {
        if (size() == 0) {
            return "[]";
        }
        final StringBuilder buf = new StringBuilder(16 * size());
        buf.append('[');

        final Iterator<E> it = iterator();
        boolean hasNext = it.hasNext();
        while (hasNext) {
            final Object value = it.next();
            buf.append(value == this ? "(this Collection)" : value);
            hasNext = it.hasNext();
            if (hasNext) {
                buf.append(", ");
            }
        }
        buf.append(']');
        return buf.toString();
    }

    //-----------------------------------------------------------------------
    /**
     * Compares two values for equals.
     * This implementation uses the equals method.
     * Subclasses can override this to match differently.
     *
     * @param value1  the first value to compare, may be null
     * @param value2  the second value to compare, may be null
     * @return true if equal
     */
    protected boolean isEqualValue(final Object value1, final Object value2) {
        return value1 == value2 || (value1 == null ? false : value1.equals(value2));
    }

    /**
     * Updates the node with a new value.
     * This implementation sets the value on the node.
     * Subclasses can override this to record the change.
     *
     * @param node  node to update
     * @param value  new value of the node
     */
    protected void updateNode(final Node<E> node, final E value) {
        node.setValue(value);
    }

    /**
     * Creates a new node with previous, next and element all set to null.
     * This implementation creates a new empty Node.
     * Subclasses can override this to create a different class.
     *
     * @return  newly created node
     */
    protected Node<E> createHeaderNode() {
        return new Node<>();
    }

    /**
     * Creates a new node with the specified properties.
     * This implementation creates a new Node with data.
     * Subclasses can override this to create a different class.
     *
     * @param value  value of the new node
     * @return a new node containing the value
     */
    protected Node<E> createNode(final E value) {
        return new Node<>(value);
    }

    /**
     * Creates a new node with the specified object as its
     * <code>value</code> and inserts it before <code>node</code>.
     * <p>
     * This implementation uses {@link #createNode(Object)} and
     * {@link #addNode(AbstractLinkedList.Node,AbstractLinkedList.Node)}.
     *
     * @param node  node to insert before
     * @param value  value of the newly added node
     * @throws NullPointerException if <code>node</code> is null
     */
    protected void addNodeBefore(final Node<E> node, final E value) {
        final Node<E> newNode = createNode(value);
        addNode(newNode, node);
    }

    /**
     * Creates a new node with the specified object as its
     * <code>value</code> and inserts it after <code>node</code>.
     * <p>
     * This implementation uses {@link #createNode(Object)} and
     * {@link #addNode(AbstractLinkedList.Node,AbstractLinkedList.Node)}.
     *
     * @param node  node to insert after
     * @param value  value of the newly added node
     * @throws NullPointerException if <code>node</code> is null
     */
    protected void addNodeAfter(final Node<E> node, final E value) {
        final Node<E> newNode = createNode(value);
        addNode(newNode, node.next);
    }

    /**
     * Inserts a new node into the list.
     *
     * @param nodeToInsert  new node to insert
     * @param insertBeforeNode  node to insert before
     * @throws NullPointerException if either node is null
     */
    protected void addNode(final Node<E> nodeToInsert, final Node<E> insertBeforeNode) {
        nodeToInsert.next = insertBeforeNode;
        nodeToInsert.previous = insertBeforeNode.previous;
        insertBeforeNode.previous.next = nodeToInsert;
        insertBeforeNode.previous = nodeToInsert;
        size++;
        modCount++;
    }

    /**
     * Removes the specified node from the list.
     *
     * @param node  the node to remove
     * @throws NullPointerException if <code>node</code> is null
     */
    protected void removeNode(final Node<E> node) {
        node.previous.next = node.next;
        node.next.previous = node.previous;
        size--;
        modCount++;
    }

    /**
     * Removes all nodes by resetting the circular list marker.
     */
    protected void removeAllNodes() {
        header.next = header;
        header.previous = header;
        size = 0;
        modCount++;
    }

    /**
     * Gets the node at a particular index.
     *
     * @param index  the index, starting from 0
     * @param endMarkerAllowed  whether or not the end marker can be returned if
     * startIndex is set to the list's size
     * @return the node at the given index
     * @throws IndexOutOfBoundsException if the index is less than 0; equal to
     * the size of the list and endMakerAllowed is false; or greater than the
     * size of the list
     */
    protected Node<E> getNode(final int index, final boolean endMarkerAllowed) throws IndexOutOfBoundsException {
        // Check the index is within the bounds
        if (index < 0) {
            throw new IndexOutOfBoundsException("Couldn't get the node: " +
                    "index (" + index + ") less than zero.");
        }
        if (!endMarkerAllowed && index == size) {
            throw new IndexOutOfBoundsException("Couldn't get the node: " +
                    "index (" + index + ") is the size of the list.");
        }
        if (index > size) {
            throw new IndexOutOfBoundsException("Couldn't get the node: " +
                    "index (" + index + ") greater than the size of the " +
                    "list (" + size + ").");
        }
        // Search the list and get the node
        Node<E> node;
        if (index < size / 2) {
            // Search forwards
            node = header.next;
            for (int currentIndex = 0; currentIndex < index; currentIndex++) {
                node = node.next;
            }
        } else {
            // Search backwards
            node = header;
            for (int currentIndex = size; currentIndex > index; currentIndex--) {
                node = node.previous;
            }
        }
        return node;
    }

    //-----------------------------------------------------------------------
    /**
     * Creates an iterator for the sublist.
     *
     * @param subList  the sublist to get an iterator for
     * @return a new iterator on the given sublist
     */
    protected Iterator<E> createSubListIterator(final LinkedSubList<E> subList) {
        return createSubListListIterator(subList, 0);
    }

    /**
     * Creates a list iterator for the sublist.
     *
     * @param subList  the sublist to get an iterator for
     * @param fromIndex  the index to start from, relative to the sublist
     * @return a new list iterator on the given sublist
     */
    protected ListIterator<E> createSubListListIterator(final LinkedSubList<E> subList, final int fromIndex) {
        return new LinkedSubListIterator<>(subList, fromIndex);
    }

    //-----------------------------------------------------------------------
    /**
     * Serializes the data held in this object to the stream specified.
     * <p>
     * The first serializable subclass must call this method from
     * <code>writeObject</code>.
     *
     * @param outputStream  the stream to write the object to
     * @throws IOException  if anything goes wrong
     */
    protected void doWriteObject(final ObjectOutputStream outputStream) throws IOException {
        // Write the size so we know how many nodes to read back
        outputStream.writeInt(size());
        for (final E e : this) {
            outputStream.writeObject(e);
        }
    }

    /**
     * Deserializes the data held in this object to the stream specified.
     * <p>
     * The first serializable subclass must call this method from
     * <code>readObject</code>.
     *
     * @param inputStream  the stream to read the object from
     * @throws IOException  if any error occurs while reading from the stream
     * @throws ClassNotFoundException  if a class read from the stream can not be loaded
     */
    @SuppressWarnings("unchecked")
    protected void doReadObject(final ObjectInputStream inputStream) throws IOException, ClassNotFoundException {
        init();
        final int size = inputStream.readInt();
        for (int i = 0; i < size; i++) {
            add((E) inputStream.readObject());
        }
    }

    //-----------------------------------------------------------------------
    /**
     * A node within the linked list.
     * <p>
     * From Commons Collections 3.1, all access to the <code>value</code> property
     * is via the methods on this class.
     */
    protected static class Node<E> {

        /** A pointer to the node before this node */
        protected Node<E> previous;
        /** A pointer to the node after this node */
        protected Node<E> next;
        /** The object contained within this node */
        protected E value;

        /**
         * Constructs a new header node.
         */
        protected Node() {
            super();
            previous = this;
            next = this;
        }

        /**
         * Constructs a new node.
         *
         * @param value  the value to store
         */
        protected Node(final E value) {
            super();
            this.value = value;
        }

        /**
         * Constructs a new node.
         *
         * @param previous  the previous node in the list
         * @param next  the next node in the list
         * @param value  the value to store
         */
        protected Node(final Node<E> previous, final Node<E> next, final E value) {
            super();
            this.previous = previous;
            this.next = next;
            this.value = value;
        }

        /**
         * Gets the value of the node.
         *
         * @return the value
         * @since 3.1
         */
        protected E getValue() {
            return value;
        }

        /**
         * Sets the value of the node.
         *
         * @param value  the value
         * @since 3.1
         */
        protected void setValue(final E value) {
            this.value = value;
        }

        /**
         * Gets the previous node.
         *
         * @return the previous node
         * @since 3.1
         */
        protected Node<E> getPreviousNode() {
            return previous;
        }

        /**
         * Sets the previous node.
         *
         * @param previous  the previous node
         * @since 3.1
         */
        protected void setPreviousNode(final Node<E> previous) {
            this.previous = previous;
        }

        /**
         * Gets the next node.
         *
         * @return the next node
         * @since 3.1
         */
        protected Node<E> getNextNode() {
            return next;
        }

        /**
         * Sets the next node.
         *
         * @param next  the next node
         * @since 3.1
         */
        protected void setNextNode(final Node<E> next) {
            this.next = next;
        }
    }

    //-----------------------------------------------------------------------
    /**
     * A list iterator over the linked list.
     */
    protected static class LinkedListIterator<E> implements ListIterator<E>, OrderedIterator<E> {

        /** The parent list */
        protected final AbstractLinkedList<E> parent;

        /**
         * The node that will be returned by {@link #next()}. If this is equal
         * to {@link AbstractLinkedList#header} then there are no more values to return.
         */
        protected Node<E> next;

        /**
         * The index of {@link #next}.
         */
        protected int nextIndex;

        /**
         * The last node that was returned by {@link #next()} or {@link
         * #previous()}. Set to <code>null</code> if {@link #next()} or {@link
         * #previous()} haven't been called, or if the node has been removed
         * with {@link #remove()} or a new node added with {@link #add(Object)}.
         * Should be accessed through {@link #getLastNodeReturned()} to enforce
         * this behaviour.
         */
        protected Node<E> current;

        /**
         * The modification count that the list is expected to have. If the list
         * doesn't have this count, then a
         * {@link java.util.ConcurrentModificationException} may be thrown by
         * the operations.
         */
        protected int expectedModCount;

        /**
         * Create a ListIterator for a list.
         *
         * @param parent  the parent list
         * @param fromIndex  the index to start at
         * @throws IndexOutOfBoundsException if fromIndex is less than 0 or greater than the size of the list
         */
        protected LinkedListIterator(final AbstractLinkedList<E> parent, final int fromIndex)
                throws IndexOutOfBoundsException {
            super();
            this.parent = parent;
            this.expectedModCount = parent.modCount;
            this.next = parent.getNode(fromIndex, true);
            this.nextIndex = fromIndex;
        }

        /**
         * Checks the modification count of the list is the value that this
         * object expects.
         *
         * @throws ConcurrentModificationException If the list's modification
         * count isn't the value that was expected.
         */
        protected void checkModCount() {
            if (parent.modCount != expectedModCount) {
                throw new ConcurrentModificationException();
            }
        }

        /**
         * Gets the last node returned.
         *
         * @return the last node returned
         * @throws IllegalStateException If {@link #next()} or {@link #previous()} haven't been called,
         * or if the node has been removed with {@link #remove()} or a new node added with {@link #add(Object)}.
         */
        protected Node<E> getLastNodeReturned() throws IllegalStateException {
            if (current == null) {
                throw new IllegalStateException();
            }
            return current;
        }

        @Override
        public boolean hasNext() {
            return next != parent.header;
        }

        @Override
        public E next() {
            checkModCount();
            if (!hasNext()) {
                throw new NoSuchElementException("No element at index " + nextIndex + ".");
            }
            final E value = next.getValue();
            current = next;
            next = next.next;
            nextIndex++;
            return value;
        }

        @Override
        public boolean hasPrevious() {
            return next.previous != parent.header;
        }

        @Override
        public E previous() {
            checkModCount();
            if (!hasPrevious()) {
                throw new NoSuchElementException("Already at start of list.");
            }
            next = next.previous;
            final E value = next.getValue();
            current = next;
            nextIndex--;
            return value;
        }

        @Override
        public int nextIndex() {
            return nextIndex;
        }

        @Override
        public int previousIndex() {
            // not normally overridden, as relative to nextIndex()
            return nextIndex() - 1;
        }

        @Override
        public void remove() {
            checkModCount();
            if (current == next) {
                // remove() following previous()
                next = next.next;
                parent.removeNode(getLastNodeReturned());
            } else {
                // remove() following next()
                parent.removeNode(getLastNodeReturned());
                nextIndex--;
            }
            current = null;
            expectedModCount++;
        }

        @Override
        public void set(final E obj) {
            checkModCount();
            getLastNodeReturned().setValue(obj);
        }

        @Override
        public void add(final E obj) {
            checkModCount();
            parent.addNodeBefore(next, obj);
            current = null;
            nextIndex++;
            expectedModCount++;
        }

    }

    //-----------------------------------------------------------------------
    /**
     * A list iterator over the linked sub list.
     */
    protected static class LinkedSubListIterator<E> extends LinkedListIterator<E> {

        /** The parent list */
        protected final LinkedSubList<E> sub;

        protected LinkedSubListIterator(final LinkedSubList<E> sub, final int startIndex) {
            super(sub.parent, startIndex + sub.offset);
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

    //-----------------------------------------------------------------------
    /**
     * The sublist implementation for AbstractLinkedList.
     */
    protected static class LinkedSubList<E> extends AbstractList<E> {
        /** The main list */
        AbstractLinkedList<E> parent;
        /** Offset from the main list */
        int offset;
        /** Sublist size */
        int size;
        /** Sublist modCount */
        int expectedModCount;

        protected LinkedSubList(final AbstractLinkedList<E> parent, final int fromIndex, final int toIndex) {
            if (fromIndex < 0) {
                throw new IndexOutOfBoundsException("fromIndex = " + fromIndex);
            }
            if (toIndex > parent.size()) {
                throw new IndexOutOfBoundsException("toIndex = " + toIndex);
            }
            if (fromIndex > toIndex) {
                throw new IllegalArgumentException("fromIndex(" + fromIndex + ") > toIndex(" + toIndex + ")");
            }
            this.parent = parent;
            this.offset = fromIndex;
            this.size = toIndex - fromIndex;
            this.expectedModCount = parent.modCount;
        }

        @Override
        public int size() {
            checkModCount();
            return size;
        }

        @Override
        public E get(final int index) {
            rangeCheck(index, size);
            checkModCount();
            return parent.get(index + offset);
        }

        @Override
        public void add(final int index, final E obj) {
            rangeCheck(index, size + 1);
            checkModCount();
            parent.add(index + offset, obj);
            expectedModCount = parent.modCount;
            size++;
            LinkedSubList.this.modCount++;
        }

        @Override
        public E remove(final int index) {
            rangeCheck(index, size);
            checkModCount();
            final E result = parent.remove(index + offset);
            expectedModCount = parent.modCount;
            size--;
            LinkedSubList.this.modCount++;
            return result;
        }

        @Override
        public boolean addAll(final Collection<? extends E> coll) {
            return addAll(size, coll);
        }

        @Override
        public boolean addAll(final int index, final Collection<? extends E> coll) {
            rangeCheck(index, size + 1);
            final int cSize = coll.size();
            if (cSize == 0) {
                return false;
            }

            checkModCount();
            parent.addAll(offset + index, coll);
            expectedModCount = parent.modCount;
            size += cSize;
            LinkedSubList.this.modCount++;
            return true;
        }

        @Override
        public E set(final int index, final E obj) {
            rangeCheck(index, size);
            checkModCount();
            return parent.set(index + offset, obj);
        }

        @Override
        public void clear() {
            checkModCount();
            final Iterator<E> it = iterator();
            while (it.hasNext()) {
                it.next();
                it.remove();
            }
        }

        @Override
        public Iterator<E> iterator() {
            checkModCount();
            return parent.createSubListIterator(this);
        }

        @Override
        public ListIterator<E> listIterator(final int index) {
            rangeCheck(index, size + 1);
            checkModCount();
            return parent.createSubListListIterator(this, index);
        }

        @Override
        public List<E> subList(final int fromIndexInclusive, final int toIndexExclusive) {
            return new LinkedSubList<>(parent, fromIndexInclusive + offset, toIndexExclusive + offset);
        }

        protected void rangeCheck(final int index, final int beyond) {
            if (index < 0 || index >= beyond) {
                throw new IndexOutOfBoundsException("Index '" + index + "' out of bounds for size '" + size + "'");
            }
        }

        protected void checkModCount() {
            if (parent.modCount != expectedModCount) {
                throw new ConcurrentModificationException();
            }
        }
    }

}
