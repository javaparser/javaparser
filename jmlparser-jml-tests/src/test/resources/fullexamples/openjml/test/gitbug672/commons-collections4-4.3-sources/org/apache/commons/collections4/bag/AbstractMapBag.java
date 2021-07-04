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
package org.apache.commons.collections4.bag;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.lang.reflect.Array;
import java.util.Collection;
import java.util.ConcurrentModificationException;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.apache.commons.collections4.Bag;
import org.apache.commons.collections4.set.UnmodifiableSet;

/**
 * Abstract implementation of the {@link Bag} interface to simplify the creation
 * of subclass implementations.
 * <p>
 * Subclasses specify a Map implementation to use as the internal storage. The
 * map will be used to map bag elements to a number; the number represents the
 * number of occurrences of that element in the bag.
 *
 * @param <E> the type of elements in this bag
 * @since 3.0 (previously DefaultMapBag v2.0)
 */
public abstract class AbstractMapBag<E> implements Bag<E> {

    /** The map to use to store the data */
    private transient Map<E, MutableInteger> map;
    /** The current total size of the bag */
    private int size;
    /** The modification count for fail fast iterators */
    private transient int modCount;
    /** Unique view of the elements */
    private transient Set<E> uniqueSet;

    /**
     * Constructor needed for subclass serialisation.
     */
    protected AbstractMapBag() {
        super();
    }

    /**
     * Constructor that assigns the specified Map as the backing store. The map
     * must be empty and non-null.
     *
     * @param map the map to assign
     */
    protected AbstractMapBag(final Map<E, MutableInteger> map) {
        super();
        this.map = map;
    }

    /**
     * Utility method for implementations to access the map that backs this bag.
     * Not intended for interactive use outside of subclasses.
     *
     * @return the map being used by the Bag
     */
    protected Map<E, MutableInteger> getMap() {
        return map;
    }

    //-----------------------------------------------------------------------
    /**
     * Returns the number of elements in this bag.
     *
     * @return current size of the bag
     */
    @Override
    public int size() {
        return size;
    }

    /**
     * Returns true if the underlying map is empty.
     *
     * @return true if bag is empty
     */
    @Override
    public boolean isEmpty() {
        return map.isEmpty();
    }

    /**
     * Returns the number of occurrence of the given element in this bag by
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
     * Determines if the bag contains the given element by checking if the
     * underlying map contains the element as a key.
     *
     * @param object the object to search for
     * @return true if the bag contains the given element
     */
    @Override
    public boolean contains(final Object object) {
        return map.containsKey(object);
    }

    /**
     * Determines if the bag contains the given elements.
     *
     * @param coll the collection to check against
     * @return <code>true</code> if the Bag contains all the collection
     */
    @Override
    public boolean containsAll(final Collection<?> coll) {
        if (coll instanceof Bag) {
            return containsAll((Bag<?>) coll);
        }
        return containsAll(new HashBag<>(coll));
    }

    /**
     * Returns <code>true</code> if the bag contains all elements in the given
     * collection, respecting cardinality.
     *
     * @param other the bag to check against
     * @return <code>true</code> if the Bag contains all the collection
     */
    boolean containsAll(final Bag<?> other) {
        final Iterator<?> it = other.uniqueSet().iterator();
        while (it.hasNext()) {
            final Object current = it.next();
            if (getCount(current) < other.getCount(current)) {
                return false;
            }
        }
        return true;
    }

    //-----------------------------------------------------------------------
    /**
     * Gets an iterator over the bag elements. Elements present in the Bag more
     * than once will be returned repeatedly.
     *
     * @return the iterator
     */
    @Override
    public Iterator<E> iterator() {
        return new BagIterator<>(this);
    }

    /**
     * Inner class iterator for the Bag.
     */
    static class BagIterator<E> implements Iterator<E> {
        private final AbstractMapBag<E> parent;
        private final Iterator<Map.Entry<E, MutableInteger>> entryIterator;
        private Map.Entry<E, MutableInteger> current;
        private int itemCount;
        private final int mods;
        private boolean canRemove;

        /**
         * Constructor.
         *
         * @param parent the parent bag
         */
        public BagIterator(final AbstractMapBag<E> parent) {
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
    /**
     * Adds a new element to the bag, incrementing its count in the underlying map.
     *
     * @param object the object to add
     * @return <code>true</code> if the object was not already in the <code>uniqueSet</code>
     */
    @Override
    public boolean add(final E object) {
        return add(object, 1);
    }

    /**
     * Adds a new element to the bag, incrementing its count in the map.
     *
     * @param object the object to search for
     * @param nCopies the number of copies to add
     * @return <code>true</code> if the object was not already in the <code>uniqueSet</code>
     */
    @Override
    public boolean add(final E object, final int nCopies) {
        modCount++;
        if (nCopies > 0) {
            final MutableInteger mut = map.get(object);
            size += nCopies;
            if (mut == null) {
                map.put(object, new MutableInteger(nCopies));
                return true;
            }
            mut.value += nCopies;
            return false;
        }
        return false;
    }

    /**
     * Invokes {@link #add(Object)} for each element in the given collection.
     *
     * @param coll the collection to add
     * @return <code>true</code> if this call changed the bag
     */
    @Override
    public boolean addAll(final Collection<? extends E> coll) {
        boolean changed = false;
        final Iterator<? extends E> i = coll.iterator();
        while (i.hasNext()) {
            final boolean added = add(i.next());
            changed = changed || added;
        }
        return changed;
    }

    //-----------------------------------------------------------------------
    /**
     * Clears the bag by clearing the underlying map.
     */
    @Override
    public void clear() {
        modCount++;
        map.clear();
        size = 0;
    }

    /**
     * Removes all copies of the specified object from the bag.
     *
     * @param object the object to remove
     * @return true if the bag changed
     */
    @Override
    public boolean remove(final Object object) {
        final MutableInteger mut = map.get(object);
        if (mut == null) {
            return false;
        }
        modCount++;
        map.remove(object);
        size -= mut.value;
        return true;
    }

    /**
     * Removes a specified number of copies of an object from the bag.
     *
     * @param object the object to remove
     * @param nCopies the number of copies to remove
     * @return true if the bag changed
     */
    @Override
    public boolean remove(final Object object, final int nCopies) {
        final MutableInteger mut = map.get(object);
        if (mut == null) {
            return false;
        }
        if (nCopies <= 0) {
            return false;
        }
        modCount++;
        if (nCopies < mut.value) {
            mut.value -= nCopies;
            size -= nCopies;
        } else {
            map.remove(object);
            size -= mut.value;
        }
        return true;
    }

    /**
     * Removes objects from the bag according to their count in the specified
     * collection.
     *
     * @param coll the collection to use
     * @return true if the bag changed
     */
    @Override
    public boolean removeAll(final Collection<?> coll) {
        boolean result = false;
        if (coll != null) {
            final Iterator<?> i = coll.iterator();
            while (i.hasNext()) {
                final boolean changed = remove(i.next(), 1);
                result = result || changed;
            }
        }
        return result;
    }

    /**
     * Remove any members of the bag that are not in the given bag, respecting
     * cardinality.
     *
     * @param coll the collection to retain
     * @return true if this call changed the collection
     */
    @Override
    public boolean retainAll(final Collection<?> coll) {
        if (coll instanceof Bag) {
            return retainAll((Bag<?>) coll);
        }
        return retainAll(new HashBag<>(coll));
    }

    /**
     * Remove any members of the bag that are not in the given bag, respecting
     * cardinality.
     * @see #retainAll(Collection)
     *
     * @param other the bag to retain
     * @return <code>true</code> if this call changed the collection
     */
    boolean retainAll(final Bag<?> other) {
        boolean result = false;
        final Bag<E> excess = new HashBag<>();
        final Iterator<E> i = uniqueSet().iterator();
        while (i.hasNext()) {
            final E current = i.next();
            final int myCount = getCount(current);
            final int otherCount = other.getCount(current);
            if (1 <= otherCount && otherCount <= myCount) {
                excess.add(current, myCount - otherCount);
            } else {
                excess.add(current, myCount);
            }
        }
        if (!excess.isEmpty()) {
            result = removeAll(excess);
        }
        return result;
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
    /**
     * Returns an array of all of this bag's elements.
     *
     * @return an array of all of this bag's elements
     */
    @Override
    public Object[] toArray() {
        final Object[] result = new Object[size()];
        int i = 0;
        final Iterator<E> it = map.keySet().iterator();
        while (it.hasNext()) {
            final E current = it.next();
            for (int index = getCount(current); index > 0; index--) {
                result[i++] = current;
            }
        }
        return result;
    }

    /**
     * Returns an array of all of this bag's elements.
     * If the input array has more elements than are in the bag,
     * trailing elements will be set to null.
     *
     * @param <T> the type of the array elements
     * @param array the array to populate
     * @return an array of all of this bag's elements
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
        final Iterator<E> it = map.keySet().iterator();
        while (it.hasNext()) {
            final E current = it.next();
            for (int index = getCount(current); index > 0; index--) {
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

    /**
     * Returns an unmodifiable view of the underlying map's key set.
     *
     * @return the set of unique elements in this bag
     */
    @Override
    public Set<E> uniqueSet() {
        if (uniqueSet == null) {
            uniqueSet = UnmodifiableSet.<E> unmodifiableSet(map.keySet());
        }
        return uniqueSet;
    }

    //-----------------------------------------------------------------------
    /**
     * Write the map out using a custom routine.
     * @param out the output stream
     * @throws IOException any of the usual I/O related exceptions
     */
    protected void doWriteObject(final ObjectOutputStream out) throws IOException {
        out.writeInt(map.size());
        for (final Entry<E, MutableInteger> entry : map.entrySet()) {
            out.writeObject(entry.getKey());
            out.writeInt(entry.getValue().value);
        }
    }

    /**
     * Read the map in using a custom routine.
     * @param map the map to use
     * @param in the input stream
     * @throws IOException any of the usual I/O related exceptions
     * @throws ClassNotFoundException if the stream contains an object which class can not be loaded
     * @throws ClassCastException if the stream does not contain the correct objects
     */
    protected void doReadObject(final Map<E, MutableInteger> map, final ObjectInputStream in)
            throws IOException, ClassNotFoundException {
        this.map = map;
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
     * Compares this Bag to another. This Bag equals another Bag if it contains
     * the same number of occurrences of the same elements.
     *
     * @param object the Bag to compare to
     * @return true if equal
     */
    @Override
    public boolean equals(final Object object) {
        if (object == this) {
            return true;
        }
        if (object instanceof Bag == false) {
            return false;
        }
        final Bag<?> other = (Bag<?>) object;
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

    /**
     * Gets a hash code for the Bag compatible with the definition of equals.
     * The hash code is defined as the sum total of a hash code for each
     * element. The per element hash code is defined as
     * <code>(e==null ? 0 : e.hashCode()) ^ noOccurances)</code>. This hash code
     * is compatible with the Set interface.
     *
     * @return the hash code of the Bag
     */
    @Override
    public int hashCode() {
        int total = 0;
        for (final Entry<E, MutableInteger> entry : map.entrySet()) {
            final E element = entry.getKey();
            final MutableInteger count = entry.getValue();
            total += (element == null ? 0 : element.hashCode()) ^ count.value;
        }
        return total;
    }

    /**
     * Implement a toString() method suitable for debugging.
     *
     * @return a debugging toString
     */
    @Override
    public String toString() {
        if (size() == 0) {
            return "[]";
        }
        final StringBuilder buf = new StringBuilder();
        buf.append('[');
        final Iterator<E> it = uniqueSet().iterator();
        while (it.hasNext()) {
            final Object current = it.next();
            final int count = getCount(current);
            buf.append(count);
            buf.append(':');
            buf.append(current);
            if (it.hasNext()) {
                buf.append(',');
            }
        }
        buf.append(']');
        return buf.toString();
    }

}
