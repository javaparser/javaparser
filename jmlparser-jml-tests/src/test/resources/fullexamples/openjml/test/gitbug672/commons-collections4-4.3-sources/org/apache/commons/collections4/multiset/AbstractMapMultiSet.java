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
import java.lang.reflect.Array;
import java.util.ConcurrentModificationException;
import java.util.Iterator;
import java.util.Map;

import org.apache.commons.collections4.MultiSet;
import org.apache.commons.collections4.iterators.AbstractIteratorDecorator;

/**
 * Abstract implementation of the {@link MultiSet} interface to simplify the
 * creation of subclass implementations.
 * <p>
 * Subclasses specify a Map implementation to use as the internal storage. The
 * map will be used to map multiset elements to a number; the number represents the
 * number of occurrences of that element in the multiset.
 *
 * @param <E> the type held in the multiset
 * @since 4.1
 */
public abstract class AbstractMapMultiSet<E> extends AbstractMultiSet<E> {

    /** The map to use to store the data */
    private transient Map<E, MutableInteger> map;
    /** The current total size of the multiset */
    private transient int size;
    /** The modification count for fail fast iterators */
    private transient int modCount;

    /**
     * Constructor needed for subclass serialisation.
     */
    protected AbstractMapMultiSet() {
        super();
    }

    /**
     * Constructor that assigns the specified Map as the backing store. The map
     * must be empty and non-null.
     *
     * @param map the map to assign
     */
    protected AbstractMapMultiSet(final Map<E, MutableInteger> map) {
        super();
        this.map = map;
    }

    /**
     * Utility method for implementations to access the map that backs this multiset.
     * Not intended for interactive use outside of subclasses.
     *
     * @return the map being used by the MultiSet
     */
    protected Map<E, MutableInteger> getMap() {
        return map;
    }

    /**
     * Sets the map being wrapped.
     * <p>
     * <b>NOTE:</b> this method should only be used during deserialization
     *
     * @param map the map to wrap
     */
    protected void setMap(final Map<E, MutableInteger> map) {
        this.map = map;
    }

    //-----------------------------------------------------------------------
    /**
     * Returns the number of elements in this multiset.
     *
     * @return current size of the multiset
     */
    @Override
    public int size() {
        return size;
    }

    /**
     * Returns true if the underlying map is empty.
     *
     * @return true if multiset is empty
     */
    @Override
    public boolean isEmpty() {
        return map.isEmpty();
    }

    /**
     * Returns the number of occurrence of the given element in this multiset by
     * looking up its count in the underlying map.
     *
     * @param object the object to search for
     * @return the number of occurrences of the object, zero if not found
     */
    @Override
    public int getCount(final Object object) {
        final MutableInteger count = map.get(object);
        if (count != null) {
            return count.value;
        }
        return 0;
    }

    //-----------------------------------------------------------------------
    /**
     * Determines if the multiset contains the given element by checking if the
     * underlying map contains the element as a key.
     *
     * @param object the object to search for
     * @return true if the multiset contains the given element
     */
    @Override
    public boolean contains(final Object object) {
        return map.containsKey(object);
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
        return new MapBasedMultiSetIterator<>(this);
    }

    /**
     * Inner class iterator for the MultiSet.
     */
    private static class MapBasedMultiSetIterator<E> implements Iterator<E> {
        private final AbstractMapMultiSet<E> parent;
        private final Iterator<Map.Entry<E, MutableInteger>> entryIterator;
        private Map.Entry<E, MutableInteger> current;
        private int itemCount;
        private final int mods;
        private boolean canRemove;

        /**
         * Constructor.
         *
         * @param parent the parent multiset
         */
        public MapBasedMultiSetIterator(final AbstractMapMultiSet<E> parent) {
            this.parent = parent;
            this.entryIterator = parent.map.entrySet().iterator();
            this.current = null;
            this.mods = parent.modCount;
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
            if (parent.modCount != mods) {
                throw new ConcurrentModificationException();
            }
            if (itemCount == 0) {
                current = entryIterator.next();
                itemCount = current.getValue().value;
            }
            canRemove = true;
            itemCount--;
            return current.getKey();
        }

        /** {@inheritDoc} */
        @Override
        public void remove() {
            if (parent.modCount != mods) {
                throw new ConcurrentModificationException();
            }
            if (canRemove == false) {
                throw new IllegalStateException();
            }
            final MutableInteger mut = current.getValue();
            if (mut.value > 1) {
                mut.value--;
            } else {
                entryIterator.remove();
            }
            parent.size--;
            canRemove = false;
        }
    }

    //-----------------------------------------------------------------------
    @Override
    public int add(final E object, final int occurrences) {
        if (occurrences < 0) {
            throw new IllegalArgumentException("Occurrences must not be negative.");
        }

        final MutableInteger mut = map.get(object);
        final int oldCount = mut != null ? mut.value : 0;

        if (occurrences > 0) {
            modCount++;
            size += occurrences;
            if (mut == null) {
                map.put(object, new MutableInteger(occurrences));
            } else {
                mut.value += occurrences;
            }
        }
        return oldCount;
    }

    //-----------------------------------------------------------------------
    /**
     * Clears the multiset by clearing the underlying map.
     */
    @Override
    public void clear() {
        modCount++;
        map.clear();
        size = 0;
    }

    @Override
    public int remove(final Object object, final int occurrences) {
        if (occurrences < 0) {
            throw new IllegalArgumentException("Occurrences must not be negative.");
        }

        final MutableInteger mut = map.get(object);
        if (mut == null) {
            return 0;
        }
        final int oldCount = mut.value;
        if (occurrences > 0) {
            modCount++;
            if (occurrences < mut.value) {
                mut.value -= occurrences;
                size -= occurrences;
            } else {
                map.remove(object);
                size -= mut.value;
            }
        }
        return oldCount;
    }

    //-----------------------------------------------------------------------
    /**
     * Mutable integer class for storing the data.
     */
    protected static class MutableInteger {
        /** The value of this mutable. */
        protected int value;

        /**
         * Constructor.
         * @param value the initial value
         */
        MutableInteger(final int value) {
            this.value = value;
        }

        @Override
        public boolean equals(final Object obj) {
            if (obj instanceof MutableInteger == false) {
                return false;
            }
            return ((MutableInteger) obj).value == value;
        }

        @Override
        public int hashCode() {
            return value;
        }
    }

    //-----------------------------------------------------------------------
    @Override
    protected Iterator<E> createUniqueSetIterator() {
        return new UniqueSetIterator<>(getMap().keySet().iterator(), this);
    }

    @Override
    protected int uniqueElements() {
        return map.size();
    }

    @Override
    protected Iterator<Entry<E>> createEntrySetIterator() {
        return new EntrySetIterator<>(map.entrySet().iterator(), this);
    }

    //-----------------------------------------------------------------------
    /**
     * Inner class UniqueSetIterator.
     */
    protected static class UniqueSetIterator<E> extends AbstractIteratorDecorator<E> {

        /** The parent multiset */
        protected final AbstractMapMultiSet<E> parent;

        /** The last returned element */
        protected E lastElement = null;

        /** Whether remove is allowed at present */
        protected boolean canRemove = false;

        /**
         * Constructor.
         * @param iterator  the iterator to decorate
         * @param parent  the parent multiset
         */
        protected UniqueSetIterator(final Iterator<E> iterator, final AbstractMapMultiSet<E> parent) {
            super(iterator);
            this.parent = parent;
        }

        @Override
        public E next() {
            lastElement = super.next();
            canRemove = true;
            return lastElement;
        }

        @Override
        public void remove() {
            if (canRemove == false) {
                throw new IllegalStateException("Iterator remove() can only be called once after next()");
            }
            final int count = parent.getCount(lastElement);
            super.remove();
            parent.remove(lastElement, count);
            lastElement = null;
            canRemove = false;
        }
    }

    /**
     * Inner class EntrySetIterator.
     */
    protected static class EntrySetIterator<E> implements Iterator<Entry<E>> {

        /** The parent map */
        protected final AbstractMapMultiSet<E> parent;

        protected final Iterator<Map.Entry<E, MutableInteger>> decorated;

        /** The last returned entry */
        protected Entry<E> last = null;

        /** Whether remove is allowed at present */
        protected boolean canRemove = false;

        /**
         * Constructor.
         * @param iterator  the iterator to decorate
         * @param parent  the parent multiset
         */
        protected EntrySetIterator(final Iterator<Map.Entry<E, MutableInteger>> iterator,
                                   final AbstractMapMultiSet<E> parent) {
            this.decorated = iterator;
            this.parent = parent;
        }

        @Override
        public boolean hasNext() {
            return decorated.hasNext();
        }

        @Override
        public Entry<E> next() {
            last = new MultiSetEntry<>(decorated.next());
            canRemove = true;
            return last;
        }

        @Override
        public void remove() {
            if (canRemove == false) {
                throw new IllegalStateException("Iterator remove() can only be called once after next()");
            }
            decorated.remove();
            last = null;
            canRemove = false;
        }
    }

    /**
     * Inner class MultiSetEntry.
     */
    protected static class MultiSetEntry<E> extends AbstractEntry<E> {

        protected final Map.Entry<E, MutableInteger> parentEntry;

        /**
         * Constructor.
         * @param parentEntry  the entry to decorate
         */
        protected MultiSetEntry(final Map.Entry<E, MutableInteger> parentEntry) {
            this.parentEntry = parentEntry;
        }

        @Override
        public E getElement() {
            return parentEntry.getKey();
        }

        @Override
        public int getCount() {
            return parentEntry.getValue().value;
        }
    }

    //-----------------------------------------------------------------------
    /**
     * Write the multiset out using a custom routine.
     * @param out the output stream
     * @throws IOException any of the usual I/O related exceptions
     */
    @Override
    protected void doWriteObject(final ObjectOutputStream out) throws IOException {
        out.writeInt(map.size());
        for (final Map.Entry<E, MutableInteger> entry : map.entrySet()) {
            out.writeObject(entry.getKey());
            out.writeInt(entry.getValue().value);
        }
    }

    /**
     * Read the multiset in using a custom routine.
     * @param in the input stream
     * @throws IOException any of the usual I/O related exceptions
     * @throws ClassNotFoundException if the stream contains an object which class can not be loaded
     * @throws ClassCastException if the stream does not contain the correct objects
     */
    @Override
    protected void doReadObject(final ObjectInputStream in)
            throws IOException, ClassNotFoundException {
        final int entrySize = in.readInt();
        for (int i = 0; i < entrySize; i++) {
            @SuppressWarnings("unchecked") // This will fail at runtime if the stream is incorrect
            final E obj = (E) in.readObject();
            final int count = in.readInt();
            map.put(obj, new MutableInteger(count));
            size += count;
        }
    }

    //-----------------------------------------------------------------------
    /**
     * Returns an array of all of this multiset's elements.
     *
     * @return an array of all of this multiset's elements
     */
    @Override
    public Object[] toArray() {
        final Object[] result = new Object[size()];
        int i = 0;
        for (final Map.Entry<E, MutableInteger> entry : map.entrySet()) {
            final E current = entry.getKey();
            final MutableInteger count = entry.getValue();
            for (int index = count.value; index > 0; index--) {
                result[i++] = current;
            }
        }
        return result;
    }

    /**
     * Returns an array of all of this multiset's elements.
     * If the input array has more elements than are in the multiset,
     * trailing elements will be set to null.
     *
     * @param <T> the type of the array elements
     * @param array the array to populate
     * @return an array of all of this multiset's elements
     * @throws ArrayStoreException if the runtime type of the specified array is not
     *   a supertype of the runtime type of the elements in this list
     * @throws NullPointerException if the specified array is null
     */
    @Override
    public <T> T[] toArray(T[] array) {
        final int size = size();
        if (array.length < size) {
            @SuppressWarnings("unchecked") // safe as both are of type T
            final T[] unchecked = (T[]) Array.newInstance(array.getClass().getComponentType(), size);
            array = unchecked;
        }

        int i = 0;
        for (final Map.Entry<E, MutableInteger> entry : map.entrySet()) {
            final E current = entry.getKey();
            final MutableInteger count = entry.getValue();
            for (int index = count.value; index > 0; index--) {
                // unsafe, will throw ArrayStoreException if types are not compatible, see javadoc
                @SuppressWarnings("unchecked")
                final T unchecked = (T) current;
                array[i++] = unchecked;
            }
        }
        while (i < array.length) {
            array[i++] = null;
        }
        return array;
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
        for (final E element : map.keySet()) {
            if (other.getCount(element) != getCount(element)) {
                return false;
            }
        }
        return true;
    }

    @Override
    public int hashCode() {
        int total = 0;
        for (final Map.Entry<E, MutableInteger> entry : map.entrySet()) {
            final E element = entry.getKey();
            final MutableInteger count = entry.getValue();
            total += (element == null ? 0 : element.hashCode()) ^ count.value;
        }
        return total;
    }
}
