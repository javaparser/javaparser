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

import java.util.Iterator;
import java.util.NavigableSet;

import org.apache.commons.collections4.Predicate;

/**
 * Decorates another <code>NavigableSet</code> to validate that all additions
 * match a specified predicate.
 * <p>
 * This set exists to provide validation for the decorated set.
 * It is normally created to decorate an empty set.
 * If an object cannot be added to the set, an IllegalArgumentException is thrown.
 * <p>
 * One usage would be to ensure that no null entries are added to the set.
 * <pre>
 * NavigableSet set =
 *   PredicatedSortedSet.predicatedNavigableSet(new TreeSet(),
 *                                              NotNullPredicate.notNullPredicate());
 * </pre>
 *
 * @param <E> the type of the elements in this set
 * @since 4.1
 */
public class PredicatedNavigableSet<E> extends PredicatedSortedSet<E> implements NavigableSet<E> {

    /** Serialization version */
    private static final long serialVersionUID = 20150528L;

    /**
     * Factory method to create a predicated (validating) navigable set.
     * <p>
     * If there are any elements already in the set being decorated, they
     * are validated.
     *
     * @param <E> the element type
     * @param set  the set to decorate, must not be null
     * @param predicate  the predicate to use for validation, must not be null
     * @return a new predicated navigable set.
     * @throws NullPointerException if set or predicate is null
     * @throws IllegalArgumentException if the set contains invalid elements
     * @since 4.0
     */
    public static <E> PredicatedNavigableSet<E> predicatedNavigableSet(final NavigableSet<E> set,
                                                                       final Predicate<? super E> predicate) {
        return new PredicatedNavigableSet<>(set, predicate);
    }

    //-----------------------------------------------------------------------
    /**
     * Constructor that wraps (not copies).
     * <p>
     * If there are any elements already in the set being decorated, they
     * are validated.
     *
     * @param set  the set to decorate, must not be null
     * @param predicate  the predicate to use for validation, must not be null
     * @throws NullPointerException if set or predicate is null
     * @throws IllegalArgumentException if the set contains invalid elements
     */
    protected PredicatedNavigableSet(final NavigableSet<E> set, final Predicate<? super E> predicate) {
        super(set, predicate);
    }

    /**
     * Gets the navigable set being decorated.
     *
     * @return the decorated navigable set
     */
    @Override
    protected NavigableSet<E> decorated() {
        return (NavigableSet<E>) super.decorated();
    }

    //-----------------------------------------------------------------------

    @Override
    public E lower(final E e) {
        return decorated().lower(e);
    }

    @Override
    public E floor(final E e) {
        return decorated().floor(e);
    }

    @Override
    public E ceiling(final E e) {
        return decorated().ceiling(e);
    }

    @Override
    public E higher(final E e) {
        return decorated().higher(e);
    }

    @Override
    public E pollFirst() {
        return decorated().pollFirst();
    }

    @Override
    public E pollLast() {
        return decorated().pollLast();
    }

    @Override
    public NavigableSet<E> descendingSet() {
        return predicatedNavigableSet(decorated().descendingSet(), predicate);
    }

    @Override
    public Iterator<E> descendingIterator() {
        return decorated().descendingIterator();
    }

    @Override
    public NavigableSet<E> subSet(final E fromElement, final boolean fromInclusive, final E toElement,
            final boolean toInclusive) {
        final NavigableSet<E> sub = decorated().subSet(fromElement, fromInclusive, toElement, toInclusive);
        return predicatedNavigableSet(sub, predicate);
    }

    @Override
    public NavigableSet<E> headSet(final E toElement, final boolean inclusive) {
        final NavigableSet<E> head = decorated().headSet(toElement, inclusive);
        return predicatedNavigableSet(head, predicate);
    }

    @Override
    public NavigableSet<E> tailSet(final E fromElement, final boolean inclusive) {
        final NavigableSet<E> tail = decorated().tailSet(fromElement, inclusive);
        return predicatedNavigableSet(tail, predicate);
    }

}
