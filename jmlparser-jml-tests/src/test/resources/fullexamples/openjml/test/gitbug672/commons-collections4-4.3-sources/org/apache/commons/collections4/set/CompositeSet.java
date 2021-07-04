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
package org.apache.commons.collections4.set;

import java.io.Serializable;
import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import org.apache.commons.collections4.CollectionUtils;
import org.apache.commons.collections4.iterators.EmptyIterator;
import org.apache.commons.collections4.iterators.IteratorChain;
import org.apache.commons.collections4.list.UnmodifiableList;

/**
 * Decorates a set of other sets to provide a single unified view.
 * <p>
 * Changes made to this set will actually be made on the decorated set.
 * Add operations require the use of a pluggable strategy.
 * If no strategy is provided then add is unsupported.
 * <p>
 * From version 4.0, this class does not extend
 * {@link org.apache.commons.collections4.collection.CompositeCollection CompositeCollection}
 * anymore due to its input restrictions (only accepts Sets).
 * See <a href="https://issues.apache.org/jira/browse/COLLECTIONS-424">COLLECTIONS-424</a>
 * for more details.
 *
 * @param <E> the type of the elements in this set
 * @since 3.0
 */
public class CompositeSet<E> implements Set<E>, Serializable {

    /** Serialization version */
    private static final long serialVersionUID = 5185069727540378940L;

    /** SetMutator to handle changes to the collection */
    private SetMutator<E> mutator;

    /** Sets in the composite */
    private final List<Set<E>> all = new ArrayList<>();

    /**
     * Create an empty CompositeSet.
     */
    public CompositeSet() {
        super();
    }

    /**
     * Create a CompositeSet with just <code>set</code> composited.
     *
     * @param set  the initial set in the composite
     */
    public CompositeSet(final Set<E> set) {
        super();
        addComposited(set);
    }

    /**
     * Create a composite set with sets as the initial set of composited Sets.
     *
     * @param sets  the initial sets in the composite
     */
    public CompositeSet(final Set<E>... sets) {
        super();
        addComposited(sets);
    }

    //-----------------------------------------------------------------------
    /**
     * Gets the size of this composite set.
     * <p>
     * This implementation calls <code>size()</code> on each set.
     *
     * @return total number of elements in all contained containers
     */
    @Override
    public int size() {
        int size = 0;
        for (final Set<E> item : all) {
            size += item.size();
        }
        return size;
    }

    /**
     * Checks whether this composite set is empty.
     * <p>
     * This implementation calls <code>isEmpty()</code> on each set.
     *
     * @return true if all of the contained sets are empty
     */
    @Override
    public boolean isEmpty() {
        for (final Set<E> item : all) {
            if (item.isEmpty() == false) {
                return false;
            }
        }
        return true;
    }

    /**
     * Checks whether this composite set contains the object.
     * <p>
     * This implementation calls <code>contains()</code> on each set.
     *
     * @param obj  the object to search for
     * @return true if obj is contained in any of the contained sets
     */
    @Override
    public boolean contains(final Object obj) {
        for (final Set<E> item : all) {
            if (item.contains(obj)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Gets an iterator over all the sets in this composite.
     * <p>
     * This implementation uses an <code>IteratorChain</code>.
     *
     * @return an <code>IteratorChain</code> instance which supports
     *  <code>remove()</code>. Iteration occurs over contained collections in
     *  the order they were added, but this behavior should not be relied upon.
     * @see IteratorChain
     */
    @Override
    public Iterator<E> iterator() {
        if (all.isEmpty()) {
            return EmptyIterator.<E>emptyIterator();
        }
        final IteratorChain<E> chain = new IteratorChain<>();
        for (final Set<E> item : all) {
            chain.addIterator(item.iterator());
        }
        return chain;
    }

    /**
     * Returns an array containing all of the elements in this composite.
     *
     * @return an object array of all the elements in the collection
     */
    @Override
    public Object[] toArray() {
        final Object[] result = new Object[size()];
        int i = 0;
        for (final Iterator<E> it = iterator(); it.hasNext(); i++) {
            result[i] = it.next();
        }
        return result;
    }

    /**
     * Returns an object array, populating the supplied array if possible.
     * See <code>Collection</code> interface for full details.
     *
     * @param <T>  the type of the elements in the collection
     * @param array  the array to use, populating if possible
     * @return an array of all the elements in the collection
     */
    @Override
    @SuppressWarnings("unchecked")
    public <T> T[] toArray(final T[] array) {
        final int size = size();
        Object[] result = null;
        if (array.length >= size) {
            result = array;
        } else {
            result = (Object[]) Array.newInstance(array.getClass().getComponentType(), size);
        }

        int offset = 0;
        for (final Collection<E> item : all) {
            for (final E e : item) {
                result[offset++] = e;
            }
        }
        if (result.length > size) {
            result[size] = null;
        }
        return (T[]) result;
    }

    /**
     * Adds an object to the collection, throwing UnsupportedOperationException
     * unless a SetMutator strategy is specified.
     *
     * @param obj  the object to add
     * @return {@code true} if the collection was modified
     * @throws UnsupportedOperationException if SetMutator hasn't been set or add is unsupported
     * @throws ClassCastException if the object cannot be added due to its type
     * @throws NullPointerException if the object cannot be added because its null
     * @throws IllegalArgumentException if the object cannot be added
     */
    @Override
    public boolean add(final E obj) {
        if (mutator == null) {
           throw new UnsupportedOperationException(
               "add() is not supported on CompositeSet without a SetMutator strategy");
        }
        return mutator.add(this, all, obj);
    }

    /**
     * If a <code>CollectionMutator</code> is defined for this CompositeSet then this
     * method will be called anyway.
     *
     * @param obj  object to be removed
     * @return true if the object is removed, false otherwise
     */
    @Override
    public boolean remove(final Object obj) {
        for (final Set<E> set : getSets()) {
            if (set.contains(obj)) {
                return set.remove(obj);
            }
        }
        return false;
    }

    /**
     * Checks whether this composite contains all the elements in the specified collection.
     * <p>
     * This implementation calls <code>contains()</code> for each element in the
     * specified collection.
     *
     * @param coll  the collection to check for
     * @return true if all elements contained
     */
    @Override
    public boolean containsAll(final Collection<?> coll) {
        for (final Object item : coll) {
            if (contains(item) == false) {
                return false;
            }
        }
        return true;
    }

    /**
     * Adds a collection of elements to this composite, throwing
     * UnsupportedOperationException unless a SetMutator strategy is specified.
     *
     * @param coll  the collection to add
     * @return true if the composite was modified
     * @throws UnsupportedOperationException if SetMutator hasn't been set or add is unsupported
     * @throws ClassCastException if the object cannot be added due to its type
     * @throws NullPointerException if the object cannot be added because its null
     * @throws IllegalArgumentException if the object cannot be added
     */
    @Override
    public boolean addAll(final Collection<? extends E> coll) {
        if (mutator == null) {
            throw new UnsupportedOperationException(
                "addAll() is not supported on CompositeSet without a SetMutator strategy");
        }
        return mutator.addAll(this, all, coll);
    }

    /**
     * Removes the elements in the specified collection from this composite set.
     * <p>
     * This implementation calls <code>removeAll</code> on each collection.
     *
     * @param coll  the collection to remove
     * @return true if the composite was modified
     * @throws UnsupportedOperationException if removeAll is unsupported
     */
    @Override
    public boolean removeAll(final Collection<?> coll) {
        if (coll.size() == 0) {
            return false;
        }
        boolean changed = false;
        for (final Collection<E> item : all) {
            changed |= item.removeAll(coll);
        }
        return changed;
    }

    /**
     * Retains all the elements in the specified collection in this composite set,
     * removing all others.
     * <p>
     * This implementation calls <code>retainAll()</code> on each collection.
     *
     * @param coll  the collection to remove
     * @return true if the composite was modified
     * @throws UnsupportedOperationException if retainAll is unsupported
     */
    @Override
    public boolean retainAll(final Collection<?> coll) {
        boolean changed = false;
        for (final Collection<E> item : all) {
            changed |= item.retainAll(coll);
        }
        return changed;
    }

    /**
     * Removes all of the elements from this composite set.
     * <p>
     * This implementation calls <code>clear()</code> on each set.
     *
     * @throws UnsupportedOperationException if clear is unsupported
     */
    @Override
    public void clear() {
        for (final Collection<E> coll : all) {
            coll.clear();
        }
    }

    //-----------------------------------------------------------------------
    /**
     * Specify a SetMutator strategy instance to handle changes.
     *
     * @param mutator  the mutator to use
     */
    public void setMutator(final SetMutator<E> mutator) {
        this.mutator = mutator;
    }

    /**
     * Add a Set to this composite.
     *
     * @param set  the set to add
     * @throws IllegalArgumentException if a SetMutator is set, but fails to resolve a collision
     * @throws UnsupportedOperationException if there is no SetMutator set
     * @throws NullPointerException if {@code set} is null
     * @see SetMutator
     */
    public synchronized void addComposited(final Set<E> set) {
        for (final Set<E> existingSet : getSets()) {
            final Collection<E> intersects = CollectionUtils.intersection(existingSet, set);
            if (intersects.size() > 0) {
                if (this.mutator == null) {
                    throw new UnsupportedOperationException(
                        "Collision adding composited set with no SetMutator set");
                }
                getMutator().resolveCollision(this, existingSet, set, intersects);
                if (CollectionUtils.intersection(existingSet, set).size() > 0) {
                    throw new IllegalArgumentException(
                        "Attempt to add illegal entry unresolved by SetMutator.resolveCollision()");
                }
            }
        }
        all.add(set);
    }

    /**
     * Add these Sets to the list of sets in this composite.
     *
     * @param set1  the first Set to be appended to the composite
     * @param set2  the second Set to be appended to the composite
     */
    public void addComposited(final Set<E> set1, final Set<E> set2) {
        addComposited(set1);
        addComposited(set2);
    }

    /**
     * Add these Sets to the list of sets in this composite
     *
     * @param sets  the Sets to be appended to the composite
     */
    public void addComposited(final Set<E>... sets) {
        for (final Set<E> set : sets) {
            addComposited(set);
        }
    }

    /**
     * Removes a set from those being decorated in this composite.
     *
     * @param set  set to be removed
     */
    public void removeComposited(final Set<E> set) {
        all.remove(set);
    }

    //-----------------------------------------------------------------------
    /**
     * Returns a new Set containing all of the elements.
     *
     * @return A new HashSet containing all of the elements in this composite.
     *   The new collection is <i>not</i> backed by this composite.
     */
    public Set<E> toSet() {
        return new HashSet<>(this);
    }

    /**
     * Gets the sets being decorated.
     *
     * @return Unmodifiable list of all sets in this composite.
     */
    public List<Set<E>> getSets() {
        return UnmodifiableList.unmodifiableList(all);
    }

    /**
     * Get the set mutator to be used for this CompositeSet.
     * @return the set mutator
     */
    protected SetMutator<E> getMutator() {
        return mutator;
    }

    /**
     * {@inheritDoc}
     * @see java.util.Set#equals
     */
    @Override
    public boolean equals(final Object obj) {
        if (obj instanceof Set) {
            final Set<?> set = (Set<?>) obj;
            return set.size() == this.size() && set.containsAll(this);
        }
        return false;
    }

    /**
     * {@inheritDoc}
     * @see java.util.Set#hashCode
     */
    @Override
    public int hashCode() {
        int code = 0;
        for (final E e : this) {
            code += e == null ? 0 : e.hashCode();
        }
        return code;
    }

    /**
     * Define callbacks for mutation operations.
     */
    public interface SetMutator<E> extends Serializable {

        /**
         * Called when an object is to be added to the composite.
         *
         * @param composite  the CompositeSet being changed
         * @param sets  all of the Set instances in this CompositeSet
         * @param obj  the object being added
         * @return true if the collection is changed
         * @throws UnsupportedOperationException if add is unsupported
         * @throws ClassCastException if the object cannot be added due to its type
         * @throws NullPointerException if the object cannot be added because its null
         * @throws IllegalArgumentException if the object cannot be added
         */
        boolean add(CompositeSet<E> composite, List<Set<E>> sets, E obj);

        /**
         * Called when a collection is to be added to the composite.
         *
         * @param composite  the CompositeSet being changed
         * @param sets  all of the Set instances in this CompositeSet
         * @param coll  the collection being added
         * @return true if the collection is changed
         * @throws UnsupportedOperationException if add is unsupported
         * @throws ClassCastException if the object cannot be added due to its type
         * @throws NullPointerException if the object cannot be added because its null
         * @throws IllegalArgumentException if the object cannot be added
         */
        boolean addAll(CompositeSet<E> composite,
                              List<Set<E>> sets,
                              Collection<? extends E> coll);

        /**
         * Called when a Set is added to the CompositeSet and there is a
         * collision between existing and added sets.
         * <p>
         * If <code>added</code> and <code>existing</code> still have any intersects
         * after this method returns an IllegalArgumentException will be thrown.
         *
         * @param comp  the CompositeSet being modified
         * @param existing  the Set already existing in the composite
         * @param added  the Set being added to the composite
         * @param intersects  the intersection of the existing and added sets
         */
        void resolveCollision(CompositeSet<E> comp,
                                     Set<E> existing,
                                     Set<E> added,
                                     Collection<E> intersects);
    }
}
