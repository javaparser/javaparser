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
package org.apache.commons.collections4;

import java.util.Collection;
import java.util.Iterator;
import java.util.Set;

/**
 * Defines a collection that counts the number of times an object appears in
 * the collection.
 * <p>
 * Suppose you have a MultiSet that contains <code>{a, a, b, c}</code>.
 * Calling {@link #getCount(Object)} on <code>a</code> would return 2, while
 * calling {@link #uniqueSet()} would return <code>{a, b, c}</code>.
 *
 * @param <E> the type held in the multiset
 * @since 4.1
 */
public interface MultiSet<E> extends Collection<E> {

    /**
     * Returns the number of occurrences of the given object currently
     * in the MultiSet. If the object does not exist in the multiset,
     * return 0.
     *
     * @param object  the object to search for
     * @return the number of occurrences of the object, zero if not found
     */
    int getCount(Object object);

    /**
     * Sets the number of occurrences of the specified object in the MultiSet
     * to the given count.
     * <p>
     * If the provided count is zero, the object will be removed from the
     * {@link #uniqueSet()}.
     *
     * @param object  the object to update
     * @param count  the number of occurrences of the object
     * @return the number of occurrences of the object before this operation, zero
     *   if the object was not contained in the multiset
     * @throws IllegalArgumentException if count is negative
     */
    int setCount(E object, int count);

    /**
     * Adds one copy of the specified object to the MultiSet.
     * <p>
     * If the object is already in the {@link #uniqueSet()} then increment its
     * count as reported by {@link #getCount(Object)}. Otherwise add it to the
     * {@link #uniqueSet()} and report its count as 1.
     *
     * @param object  the object to add
     * @return <code>true</code> always, as the size of the MultiSet is increased
     *   in any case
     */
    @Override
    boolean add(E object);

    /**
     * Adds a number of occurrences of the specified object to the MultiSet.
     * <p>
     * If the object is already in the {@link #uniqueSet()} then increment its
     * count as reported by {@link #getCount(Object)}. Otherwise add it to the
     * {@link #uniqueSet()} and report its count as <code>occurrences</code>.
     *
     * @param object  the object to add
     * @param occurrences  the number of occurrences to add, may be zero,
     *   in which case no change is made to the multiset
     * @return the number of occurrences of the object in the multiset before
     *   this operation; possibly zero
     * @throws IllegalArgumentException if occurrences is negative
     */
    int add(E object, int occurrences);

    /**
     * Removes one occurrence of the given object from the MultiSet.
     * <p>
     * If the number of occurrences after this operations is reduced
     * to zero, the object will be removed from the {@link #uniqueSet()}.
     *
     * @param object  the object to remove
     * @return <code>true</code> if this call changed the collection
     */
    @Override
    boolean remove(Object object);

    /**
     * Removes a number of occurrences of the specified object from the MultiSet.
     * <p>
     * If the number of occurrences to remove is greater than the actual number of
     * occurrences in the multiset, the object will be removed from the multiset.
     *
     * @param object  the object to remove
     * @param occurrences  the number of occurrences to remove, may be zero,
     *   in which case no change is made to the multiset
     * @return the number of occurrences of the object in the multiset
     *   before the operation; possibly zero
     * @throws IllegalArgumentException if occurrences is negative
     */
    int remove(Object object, int occurrences);

    /**
     * Returns a {@link Set} of unique elements in the MultiSet.
     * <p>
     * Uniqueness constraints are the same as those in {@link java.util.Set}.
     * <p>
     * The returned set is backed by this multiset, so any change to either
     * is immediately reflected in the other. Only removal operations are
     * supported, in which case all occurrences of the element are removed
     * from the backing multiset.
     *
     * @return the Set of unique MultiSet elements
     */
    Set<E> uniqueSet();

    /**
     * Returns a {@link Set} of all entries contained in the MultiSet.
     * <p>
     * The returned set is backed by this multiset, so any change to either
     * is immediately reflected in the other.
     *
     * @return the Set of MultiSet entries
     */
    Set<Entry<E>> entrySet();

    /**
     * Returns an {@link Iterator} over the entire set of members,
     * including copies due to cardinality. This iterator is fail-fast
     * and will not tolerate concurrent modifications.
     *
     * @return iterator over all elements in the MultiSet
     */
    @Override
    Iterator<E> iterator();

    /**
     * Returns the total number of items in the MultiSet.
     *
     * @return the total size of the multiset
     */
    @Override
    int size();

    /**
     * Returns <code>true</code> if the MultiSet contains at least one
     * occurrence for each element contained in the given collection.
     *
     * @param coll  the collection to check against
     * @return <code>true</code> if the MultiSet contains all the collection
     */
    @Override
    boolean containsAll(Collection<?> coll);

    /**
     * Remove all occurrences of all elements from this MultiSet represented
     * in the given collection.
     *
     * @param coll  the collection of elements to remove
     * @return <code>true</code> if this call changed the multiset
     */
    @Override
    boolean removeAll(Collection<?> coll);

    /**
     * Remove any elements of this MultiSet that are not contained in the
     * given collection.
     *
     * @param coll  the collection of elements to retain
     * @return <code>true</code> if this call changed the multiset
     */
    @Override
    boolean retainAll(Collection<?> coll);

    /**
     * Compares this MultiSet to another object.
     * <p>
     * This MultiSet equals another object if it is also a MultiSet
     * that contains the same number of occurrences of the same elements.
     *
     * @param obj  the object to compare to
     * @return true if equal
     */
    @Override
    boolean equals(Object obj);

    /**
     * Gets a hash code for the MultiSet compatible with the definition of equals.
     * The hash code is defined as the sum total of a hash code for each element.
     * The per element hash code is defined as
     * <code>(e==null ? 0 : e.hashCode()) ^ noOccurances)</code>.
     *
     * @return the hash code of the MultiSet
     */
    @Override
    int hashCode();

    /**
     * An unmodifiable entry for an element and its occurrence as contained in a MultiSet.
     * <p>
     * The {@link MultiSet#entrySet()} method returns a view of the multiset whose elements
     * implements this interface.
     *
     * @param <E>  the element type
     */
    interface Entry<E> {

        /**
         * Returns the element corresponding to this entry.
         *
         * @return the element corresponding to this entry
         */
        E getElement();

        /**
         * Returns the number of occurrences for the element of this entry.
         *
         * @return the number of occurrences of the element
         */
        int getCount();

        /**
         * Compares the specified object with this entry for equality.
         * Returns true if the given object is also a multiset entry
         * and the two entries represent the same element with the same
         * number of occurrences.
         * <p>
         * More formally, two entries <code>e1</code> and <code>e2</code> represent
         * the same mapping if
         * <pre>
         *     (e1.getElement()==null ? e2.getElement()==null
         *                            : e1.getElement().equals(e2.getElement())) &amp;&amp;
         *     (e1.getCount()==e2.getCount())
         * </pre>
         *
         * @param o object to be compared for equality with this multiset entry
         * @return true if the specified object is equal to this multiset entry
         */
        @Override
        boolean equals(Object o);

        /**
         * Returns the hash code value for this multiset entry.
         * <p>
         * The hash code of a multiset entry <code>e</code> is defined to be:
         * <pre>
         *      (e==null ? 0 : e.hashCode()) ^ noOccurances)
         * </pre>
         *
         * @return the hash code value for this multiset entry
         */
        @Override
        int hashCode();
    }

}
