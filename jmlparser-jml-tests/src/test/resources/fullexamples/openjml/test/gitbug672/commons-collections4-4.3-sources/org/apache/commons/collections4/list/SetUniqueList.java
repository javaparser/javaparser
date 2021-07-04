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

import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
import java.util.Set;

import org.apache.commons.collections4.ListUtils;
import org.apache.commons.collections4.iterators.AbstractIteratorDecorator;
import org.apache.commons.collections4.iterators.AbstractListIteratorDecorator;
import org.apache.commons.collections4.set.UnmodifiableSet;

/**
 * Decorates a <code>List</code> to ensure that no duplicates are present much
 * like a <code>Set</code>.
 * <p>
 * The <code>List</code> interface makes certain assumptions/requirements. This
 * implementation breaks these in certain ways, but this is merely the result of
 * rejecting duplicates. Each violation is explained in the method, but it
 * should not affect you. Bear in mind that Sets require immutable objects to
 * function correctly.
 * <p>
 * The {@link org.apache.commons.collections4.set.ListOrderedSet ListOrderedSet}
 * class provides an alternative approach, by wrapping an existing Set and
 * retaining insertion order in the iterator.
 * <p>
 * This class is Serializable from Commons Collections 3.1.
 *
 * @since 3.0
 */
public class SetUniqueList<E> extends AbstractSerializableListDecorator<E> {

    /** Serialization version. */
    private static final long serialVersionUID = 7196982186153478694L;

    /** Internal Set to maintain uniqueness. */
    private final Set<E> set;

    /**
     * Factory method to create a SetList using the supplied list to retain order.
     * <p>
     * If the list contains duplicates, these are removed (first indexed one
     * kept). A <code>HashSet</code> is used for the set behaviour.
     *
     * @param <E>  the element type
     * @param list  the list to decorate, must not be null
     * @return a new {@link SetUniqueList}
     * @throws NullPointerException if list is null
     * @since 4.0
     */
    public static <E> SetUniqueList<E> setUniqueList(final List<E> list) {
        if (list == null) {
            throw new NullPointerException("List must not be null");
        }
        if (list.isEmpty()) {
            return new SetUniqueList<>(list, new HashSet<E>());
        }
        final List<E> temp = new ArrayList<>(list);
        list.clear();
        final SetUniqueList<E> sl = new SetUniqueList<>(list, new HashSet<E>());
        sl.addAll(temp);
        return sl;
    }

    // -----------------------------------------------------------------------
    /**
     * Constructor that wraps (not copies) the List and specifies the set to use.
     * <p>
     * The set and list must both be correctly initialised to the same elements.
     *
     * @param set  the set to decorate, must not be null
     * @param list  the list to decorate, must not be null
     * @throws NullPointerException if set or list is null
     */
    protected SetUniqueList(final List<E> list, final Set<E> set) {
        super(list);
        if (set == null) {
            throw new NullPointerException("Set must not be null");
        }
        this.set = set;
    }

    // -----------------------------------------------------------------------
    /**
     * Gets an unmodifiable view as a Set.
     *
     * @return an unmodifiable set view
     */
    public Set<E> asSet() {
        return UnmodifiableSet.unmodifiableSet(set);
    }

    // -----------------------------------------------------------------------
    /**
     * Adds an element to the list if it is not already present.
     * <p>
     * <i>(Violation)</i> The <code>List</code> interface requires that this
     * method returns <code>true</code> always. However this class may return
     * <code>false</code> because of the <code>Set</code> behaviour.
     *
     * @param object  the object to add
     * @return true if object was added
     */
    @Override
    public boolean add(final E object) {
        // gets initial size
        final int sizeBefore = size();

        // adds element if unique
        add(size(), object);

        // compares sizes to detect if collection changed
        return sizeBefore != size();
    }

    /**
     * Adds an element to a specific index in the list if it is not already
     * present.
     * <p>
     * <i>(Violation)</i> The <code>List</code> interface makes the assumption
     * that the element is always inserted. This may not happen with this
     * implementation.
     *
     * @param index  the index to insert at
     * @param object  the object to add
     */
    @Override
    public void add(final int index, final E object) {
        // adds element if it is not contained already
        if (set.contains(object) == false) {
            set.add(object);
            super.add(index, object);
        }
    }

    /**
     * Adds a collection of objects to the end of the list avoiding duplicates.
     * <p>
     * Only elements that are not already in this list will be added, and
     * duplicates from the specified collection will be ignored.
     * <p>
     * <i>(Violation)</i> The <code>List</code> interface makes the assumption
     * that the elements are always inserted. This may not happen with this
     * implementation.
     *
     * @param coll  the collection to add in iterator order
     * @return true if this collection changed
     */
    @Override
    public boolean addAll(final Collection<? extends E> coll) {
        return addAll(size(), coll);
    }

    /**
     * Adds a collection of objects a specific index in the list avoiding
     * duplicates.
     * <p>
     * Only elements that are not already in this list will be added, and
     * duplicates from the specified collection will be ignored.
     * <p>
     * <i>(Violation)</i> The <code>List</code> interface makes the assumption
     * that the elements are always inserted. This may not happen with this
     * implementation.
     *
     * @param index  the index to insert at
     * @param coll  the collection to add in iterator order
     * @return true if this collection changed
     */
    @Override
    public boolean addAll(final int index, final Collection<? extends E> coll) {
        final List<E> temp = new ArrayList<>();
        for (final E e : coll) {
            if (set.add(e)) {
                temp.add(e);
            }
        }
        return super.addAll(index, temp);
    }

    // -----------------------------------------------------------------------
    /**
     * Sets the value at the specified index avoiding duplicates.
     * <p>
     * The object is set into the specified index. Afterwards, any previous
     * duplicate is removed. If the object is not already in the list then a
     * normal set occurs. If it is present, then the old version is removed.
     *
     * @param index  the index to insert at
     * @param object  the object to set
     * @return the previous object
     */
    @Override
    public E set(final int index, final E object) {
        final int pos = indexOf(object);
        final E removed = super.set(index, object);

        if (pos != -1 && pos != index) {
            // the object is already in the unique list
            // (and it hasn't been swapped with itself)
            super.remove(pos); // remove the duplicate by index
        }

        set.remove(removed); // remove the item deleted by the set
        set.add(object); // add the new item to the unique set

        return removed; // return the item deleted by the set
    }

    @Override
    public boolean remove(final Object object) {
        final boolean result = set.remove(object);
        if (result) {
            super.remove(object);
        }
        return result;
    }

    @Override
    public E remove(final int index) {
        final E result = super.remove(index);
        set.remove(result);
        return result;
    }

    @Override
    public boolean removeAll(final Collection<?> coll) {
        boolean result = false;
        for (final Object name : coll) {
            result |= remove(name);
        }
        return result;
    }

    /**
     * {@inheritDoc}
     * <p>
     * This implementation iterates over the elements of this list, checking
     * each element in turn to see if it's contained in <code>coll</code>.
     * If it's not contained, it's removed from this list. As a consequence,
     * it is advised to use a collection type for <code>coll</code> that provides
     * a fast (e.g. O(1)) implementation of {@link Collection#contains(Object)}.
     */
    @Override
    public boolean retainAll(final Collection<?> coll) {
        final boolean result = set.retainAll(coll);
        if (result == false) {
            return false;
        }
        if (set.size() == 0) {
            super.clear();
        } else {
            // use the set as parameter for the call to retainAll to improve performance
            super.retainAll(set);
        }
        return result;
    }

    @Override
    public void clear() {
        super.clear();
        set.clear();
    }

    @Override
    public boolean contains(final Object object) {
        return set.contains(object);
    }

    @Override
    public boolean containsAll(final Collection<?> coll) {
        return set.containsAll(coll);
    }

    @Override
    public Iterator<E> iterator() {
        return new SetListIterator<>(super.iterator(), set);
    }

    @Override
    public ListIterator<E> listIterator() {
        return new SetListListIterator<>(super.listIterator(), set);
    }

    @Override
    public ListIterator<E> listIterator(final int index) {
        return new SetListListIterator<>(super.listIterator(index), set);
    }

    /**
     * {@inheritDoc}
     * <p>
     * NOTE: from 4.0, an unmodifiable list will be returned, as changes to the
     * subList can invalidate the parent list.
     */
    @Override
    public List<E> subList(final int fromIndex, final int toIndex) {
        final List<E> superSubList = super.subList(fromIndex, toIndex);
        final Set<E> subSet = createSetBasedOnList(set, superSubList);
        return ListUtils.unmodifiableList(new SetUniqueList<>(superSubList, subSet));
    }

    /**
     * Create a new {@link Set} with the same type as the provided {@code set}
     * and populate it with all elements of {@code list}.
     *
     * @param set  the {@link Set} to be used as return type, must not be null
     * @param list  the {@link List} to populate the {@link Set}
     * @return a new {@link Set} populated with all elements of the provided
     *   {@link List}
     */
    protected Set<E> createSetBasedOnList(final Set<E> set, final List<E> list) {
        Set<E> subSet;
        if (set.getClass().equals(HashSet.class)) {
            subSet = new HashSet<>(list.size());
        } else {
            try {
                subSet = set.getClass().getDeclaredConstructor(set.getClass()).newInstance(set);
            } catch (final InstantiationException
                    | IllegalAccessException
                    | InvocationTargetException
                    | NoSuchMethodException ie) {
                subSet = new HashSet<>();
            }
        }
        return subSet;
    }

    // -----------------------------------------------------------------------
    /**
     * Inner class iterator.
     */
    static class SetListIterator<E> extends AbstractIteratorDecorator<E> {

        private final Set<E> set;
        private E last = null;

        protected SetListIterator(final Iterator<E> it, final Set<E> set) {
            super(it);
            this.set = set;
        }

        @Override
        public E next() {
            last = super.next();
            return last;
        }

        @Override
        public void remove() {
            super.remove();
            set.remove(last);
            last = null;
        }
    }

    /**
     * Inner class iterator.
     */
    static class SetListListIterator<E> extends
            AbstractListIteratorDecorator<E> {

        private final Set<E> set;
        private E last = null;

        protected SetListListIterator(final ListIterator<E> it, final Set<E> set) {
            super(it);
            this.set = set;
        }

        @Override
        public E next() {
            last = super.next();
            return last;
        }

        @Override
        public E previous() {
            last = super.previous();
            return last;
        }

        @Override
        public void remove() {
            super.remove();
            set.remove(last);
            last = null;
        }

        @Override
        public void add(final E object) {
            if (set.contains(object) == false) {
                super.add(object);
                set.add(object);
            }
        }

        @Override
        public void set(final E object) {
            throw new UnsupportedOperationException("ListIterator does not support set");
        }
    }

}
