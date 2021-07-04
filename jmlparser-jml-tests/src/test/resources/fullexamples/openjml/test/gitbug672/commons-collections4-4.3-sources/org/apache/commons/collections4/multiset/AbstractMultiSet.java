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
package org.apache.commons.collections4.multiset;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.util.AbstractCollection;
import java.util.AbstractSet;
import java.util.Collection;
import java.util.Iterator;
import java.util.Set;

import org.apache.commons.collections4.IteratorUtils;
import org.apache.commons.collections4.MultiSet;
import org.apache.commons.collections4.Transformer;

/**
 * Abstract implementation of the {@link MultiSet} interface to simplify the
 * creation of subclass implementations.
 *
 * @param <E> the type held in the multiset
 * @since 4.1
 */
public abstract class AbstractMultiSet<E> extends AbstractCollection<E> implements MultiSet<E> {

    /** View of the elements */
    private transient Set<E> uniqueSet;
    /** View of the entries */
    private transient Set<Entry<E>> entrySet;

    /**
     * Constructor needed for subclass serialisation.
     */
    protected AbstractMultiSet() {
        super();
    }

    //-----------------------------------------------------------------------
    /**
     * Returns the number of elements in this multiset.
     *
     * @return current size of the multiset
     */
    @Override
    public int size() {
        int totalSize = 0;
        for (final Entry<E> entry : entrySet()) {
            totalSize += entry.getCount();
        }
        return totalSize;
    }

    /**
     * Returns the number of occurrence of the given element in this multiset by
     * iterating over its entrySet.
     *
     * @param object the object to search for
     * @return the number of occurrences of the object, zero if not found
     */
    @Override
    public int getCount(final Object object) {
        for (final Entry<E> entry : entrySet()) {
            final E element = entry.getElement();
            if (element == object ||
                element != null && element.equals(object)) {
                return entry.getCount();
            }
        }
        return 0;
    }

    @Override
    public int setCount(final E object, final int count) {
        if (count < 0) {
            throw new IllegalArgumentException("Count must not be negative.");
        }

        final int oldCount = getCount(object);
        if (oldCount < count) {
            add(object, count - oldCount);
        } else {
            remove(object, oldCount - count);
        }
        return oldCount;
    }

    //-----------------------------------------------------------------------
    /**
     * Determines if the multiset contains the given element.
     *
     * @param object the object to search for
     * @return true if the multiset contains the given element
     */
    @Override
    public boolean contains(final Object object) {
        return getCount(object) > 0;
    }

    //-----------------------------------------------------------------------
    /**
     * Gets an iterator over the multiset elements. Elements present in the
     * MultiSet more than once will be returned repeatedly.
     *
     * @return the iterator
     */
    @Override
    public Iterator<E> iterator() {
        return new MultiSetIterator<>(this);
    }

    /**
     * Inner class iterator for the MultiSet.
     */
    private static class MultiSetIterator<E> implements Iterator<E> {
        private final AbstractMultiSet<E> parent;
        private final Iterator<Entry<E>> entryIterator;
        private Entry<E> current;
        private int itemCount;
        private boolean canRemove;

        /**
         * Constructor.
         *
         * @param parent the parent multiset
         */
        public MultiSetIterator(final AbstractMultiSet<E> parent) {
            this.parent = parent;
            this.entryIterator = parent.entrySet().iterator();
            this.current = null;
            this.canRemove = false;
        }

        /** {@inheritDoc} */
        @Override
        public boolean hasNext() {
            return itemCount > 0 || entryIterator.hasNext();
        }

        /** {@inheritDoc} */
        @Override
        public E next() {
            if (itemCount == 0) {
                current = entryIterator.next();
                itemCount = current.getCount();
            }
            canRemove = true;
            itemCount--;
            return current.getElement();
        }

        /** {@inheritDoc} */
        @Override
        public void remove() {
            if (canRemove == false) {
                throw new IllegalStateException();
            }
            final int count = current.getCount();
            if (count > 1) {
                parent.remove(current.getElement());
            } else {
                entryIterator.remove();
            }
            canRemove = false;
        }
    }

    //-----------------------------------------------------------------------
    @Override
    public boolean add(final E object) {
        add(object, 1);
        return true;
    }

    @Override
    public int add(final E object, final int occurrences) {
        throw new UnsupportedOperationException();
    }

    //-----------------------------------------------------------------------
    /**
     * Clears the multiset removing all elements from the entrySet.
     */
    @Override
    public void clear() {
        final Iterator<Entry<E>> it = entrySet().iterator();
        while (it.hasNext()) {
            it.next();
            it.remove();
        }
    }

    @Override
    public boolean remove(final Object object) {
        return remove(object, 1) != 0;
    }

    @Override
    public int remove(final Object object, final int occurrences) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean removeAll(final Collection<?> coll) {
        boolean result = false;
        final Iterator<?> i = coll.iterator();
        while (i.hasNext()) {
            final Object obj = i.next();
            final boolean changed = remove(obj, getCount(obj)) != 0;
            result = result || changed;
        }
        return result;
    }

    //-----------------------------------------------------------------------
    /**
     * Returns a view of the unique elements of this multiset.
     *
     * @return the set of unique elements in this multiset
     */
    @Override
    public Set<E> uniqueSet() {
        if (uniqueSet == null) {
            uniqueSet = createUniqueSet();
        }
        return uniqueSet;
    }

    /**
     * Create a new view for the set of unique elements in this multiset.
     *
     * @return a view of the set of unique elements
     */
    protected Set<E> createUniqueSet() {
        return new UniqueSet<>(this);
    }

    /**
     * Creates a unique set iterator.
     * Subclasses can override this to return iterators with different properties.
     *
     * @return the uniqueSet iterator
     */
    protected Iterator<E> createUniqueSetIterator() {
        final Transformer<Entry<E>, E> transformer = new Transformer<Entry<E>, E>() {
            @Override
            public E transform(final Entry<E> entry) {
                return entry.getElement();
            }
        };
        return IteratorUtils.transformedIterator(entrySet().iterator(), transformer);
    }

    /**
     * Returns an unmodifiable view of the entries of this multiset.
     *
     * @return the set of entries in this multiset
     */
    @Override
    public Set<Entry<E>> entrySet() {
        if (entrySet == null) {
            entrySet = createEntrySet();
        }
        return entrySet;
    }

    /**
     * Create a new view for the set of entries in this multiset.
     *
     * @return a view of the set of entries
     */
    protected Set<Entry<E>> createEntrySet() {
        return new EntrySet<>(this);
    }

    /**
     * Returns the number of unique elements in this multiset.
     *
     * @return the number of unique elements
     */
    protected abstract int uniqueElements();

    /**
     * Creates an entry set iterator.
     * Subclasses can override this to return iterators with different properties.
     *
     * @return the entrySet iterator
     */
    protected abstract Iterator<Entry<E>> createEntrySetIterator();

    //-----------------------------------------------------------------------
    /**
     * Inner class UniqueSet.
     */
    protected static class UniqueSet<E> extends AbstractSet<E> {

        /** The parent multiset */
        protected final AbstractMultiSet<E> parent;

        /**
         * Constructs a new unique element view of the MultiSet.
         *
         * @param parent  the parent MultiSet
         */
        protected UniqueSet(final AbstractMultiSet<E> parent) {
            this.parent = parent;
        }

        @Override
        public Iterator<E> iterator() {
            return parent.createUniqueSetIterator();
        }

        @Override
        public boolean contains(final Object key) {
            return parent.contains(key);
        }

        @Override
        public boolean containsAll(final Collection<?> coll) {
            return parent.containsAll(coll);
        }

        @Override
        public boolean remove(final Object key) {
            return parent.remove(key, parent.getCount(key)) != 0;
        }

        @Override
        public int size() {
            return parent.uniqueElements();
        }

        @Override
        public void clear() {
            parent.clear();
        }
    }

    //-----------------------------------------------------------------------
    /**
     * Inner class EntrySet.
     */
    protected static class EntrySet<E> extends AbstractSet<Entry<E>> {

        private final AbstractMultiSet<E> parent;

        /**
         * Constructs a new view of the MultiSet.
         *
         * @param parent  the parent MultiSet
         */
        protected EntrySet(final AbstractMultiSet<E> parent) {
            this.parent = parent;
        }

        @Override
        public int size() {
            return parent.uniqueElements();
        }

        @Override
        public Iterator<Entry<E>> iterator() {
            return parent.createEntrySetIterator();
        }

        @Override
        public boolean contains(final Object obj) {
            if (obj instanceof Entry<?> == false) {
                return false;
            }
            final Entry<?> entry = (Entry<?>) obj;
            final Object element = entry.getElement();
            return parent.getCount(element) == entry.getCount();
        }

        @Override
        public boolean remove(final Object obj) {
            if (obj instanceof Entry<?> == false) {
                return false;
            }
            final Entry<?> entry = (Entry<?>) obj;
            final Object element = entry.getElement();
            if (parent.contains(element)) {
                final int count = parent.getCount(element);
                if (entry.getCount() == count) {
                    parent.remove(element, count);
                    return true;
                }
            }
            return false;
        }
    }

    /**
     * Inner class AbstractEntry.
     */
    protected static abstract class AbstractEntry<E> implements Entry<E> {

        @Override
        public boolean equals(final Object object) {
          if (object instanceof Entry) {
            final Entry<?> other = (Entry<?>) object;
            final E element = this.getElement();
            final Object otherElement = other.getElement();

            return this.getCount() == other.getCount() &&
                   (element == otherElement ||
                    element != null && element.equals(otherElement));
          }
          return false;
        }

        @Override
        public int hashCode() {
          final E element = getElement();
          return ((element == null) ? 0 : element.hashCode()) ^ getCount();
        }

        @Override
        public String toString() {
            return String.format("%s:%d", getElement(), getCount());
        }

    }

    //-----------------------------------------------------------------------
    /**
     * Write the multiset out using a custom routine.
     * @param out the output stream
     * @throws IOException any of the usual I/O related exceptions
     */
    protected void doWriteObject(final ObjectOutputStream out) throws IOException {
        out.writeInt(entrySet().size());
        for (final Entry<E> entry : entrySet()) {
            out.writeObject(entry.getElement());
            out.writeInt(entry.getCount());
        }
    }

    /**
     * Read the multiset in using a custom routine.
     * @param in the input stream
     * @throws IOException any of the usual I/O related exceptions
     * @throws ClassNotFoundException if the stream contains an object which class can not be loaded
     * @throws ClassCastException if the stream does not contain the correct objects
     */
    protected void doReadObject(final ObjectInputStream in)
            throws IOException, ClassNotFoundException {
        final int entrySize = in.readInt();
        for (int i = 0; i < entrySize; i++) {
            @SuppressWarnings("unchecked") // This will fail at runtime if the stream is incorrect
            final E obj = (E) in.readObject();
            final int count = in.readInt();
            setCount(obj, count);
        }
    }

    //-----------------------------------------------------------------------
    @Override
    public boolean equals(final Object object) {
        if (object == this) {
            return true;
        }
        if (object instanceof MultiSet == false) {
            return false;
        }
        final MultiSet<?> other = (MultiSet<?>) object;
        if (other.size() != size()) {
            return false;
        }
        for (final Entry<E> entry : entrySet()) {
            if (other.getCount(entry.getElement()) != getCount(entry.getElement())) {
                return false;
            }
        }
        return true;
    }

    @Override
    public int hashCode() {
        return entrySet().hashCode();
    }

    /**
     * Implement a toString() method suitable for debugging.
     *
     * @return a debugging toString
     */
    @Override
    public String toString() {
        return entrySet().toString();
    }

}
