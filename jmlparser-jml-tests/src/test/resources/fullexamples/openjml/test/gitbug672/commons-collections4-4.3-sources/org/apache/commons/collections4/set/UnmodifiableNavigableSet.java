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

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.util.Collection;
import java.util.Iterator;
import java.util.NavigableSet;
import java.util.SortedSet;

import org.apache.commons.collections4.Unmodifiable;
import org.apache.commons.collections4.iterators.UnmodifiableIterator;

/**
 * Decorates another <code>NavigableSet</code> to ensure it can't be altered.
 * <p>
 * Attempts to modify it will result in an UnsupportedOperationException.
 *
 * @param <E> the type of the elements in this set
 * @since 4.1
 */
public final class UnmodifiableNavigableSet<E>
        extends AbstractNavigableSetDecorator<E>
        implements Unmodifiable {

    /** Serialization version */
    private static final long serialVersionUID = 20150528L;

    /**
     * Factory method to create an unmodifiable set.
     *
     * @param <E> the element type
     * @param set  the set to decorate, must not be null
     * @return a new unmodifiable {@link NavigableSet}
     * @throws NullPointerException if set is null
     */
    public static <E> NavigableSet<E> unmodifiableNavigableSet(final NavigableSet<E> set) {
        if (set instanceof Unmodifiable) {
            return set;
        }
        return new UnmodifiableNavigableSet<>(set);
    }

    //-----------------------------------------------------------------------
    /**
     * Constructor that wraps (not copies).
     *
     * @param set  the set to decorate, must not be null
     * @throws NullPointerException if set is null
     */
    private UnmodifiableNavigableSet(final NavigableSet<E> set) {
        super(set);
    }

    //-----------------------------------------------------------------------
    @Override
    public Iterator<E> iterator() {
        return UnmodifiableIterator.unmodifiableIterator(decorated().iterator());
    }

    @Override
    public boolean add(final E object) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean addAll(final Collection<? extends E> coll) {
        throw new UnsupportedOperationException();
    }

    @Override
    public void clear() {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean remove(final Object object) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean removeAll(final Collection<?> coll) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean retainAll(final Collection<?> coll) {
        throw new UnsupportedOperationException();
    }

    // SortedSet
    //-----------------------------------------------------------------------
    @Override
    public SortedSet<E> subSet(final E fromElement, final E toElement) {
        final SortedSet<E> sub = decorated().subSet(fromElement, toElement);
        return UnmodifiableSortedSet.unmodifiableSortedSet(sub);
    }

    @Override
    public SortedSet<E> headSet(final E toElement) {
        final SortedSet<E> head = decorated().headSet(toElement);
        return UnmodifiableSortedSet.unmodifiableSortedSet(head);
    }

    @Override
    public SortedSet<E> tailSet(final E fromElement) {
        final SortedSet<E> tail = decorated().tailSet(fromElement);
        return UnmodifiableSortedSet.unmodifiableSortedSet(tail);
    }

    // NavigableSet
    //-----------------------------------------------------------------------
    @Override
    public NavigableSet<E> descendingSet() {
        return unmodifiableNavigableSet(decorated().descendingSet());
    }

    @Override
    public Iterator<E> descendingIterator() {
        return UnmodifiableIterator.unmodifiableIterator(decorated().descendingIterator());
    }

    @Override
    public NavigableSet<E> subSet(final E fromElement, final boolean fromInclusive, final E toElement,
            final boolean toInclusive) {
        final NavigableSet<E> sub = decorated().subSet(fromElement, fromInclusive, toElement, toInclusive);
        return unmodifiableNavigableSet(sub);
    }

    @Override
    public NavigableSet<E> headSet(final E toElement, final boolean inclusive) {
        final NavigableSet<E> head = decorated().headSet(toElement, inclusive);
        return unmodifiableNavigableSet(head);
    }

    @Override
    public NavigableSet<E> tailSet(final E fromElement, final boolean inclusive) {
        final NavigableSet<E> tail = decorated().tailSet(fromElement, inclusive);
        return unmodifiableNavigableSet(tail);
    }

    //-----------------------------------------------------------------------
    /**
     * Write the collection out using a custom routine.
     *
     * @param out  the output stream
     * @throws IOException if an error occurs while writing to the stream
     */
    private void writeObject(final ObjectOutputStream out) throws IOException {
        out.defaultWriteObject();
        out.writeObject(decorated());
    }

    /**
     * Read the collection in using a custom routine.
     *
     * @param in  the input stream
     * @throws IOException if an error occurs while reading from the stream
     * @throws ClassNotFoundException if an object read from the stream can not be loaded
     */
    @SuppressWarnings("unchecked") // (1) should only fail if input stream is incorrect
    private void readObject(final ObjectInputStream in) throws IOException, ClassNotFoundException {
        in.defaultReadObject();
        setCollection((Collection<E>) in.readObject()); // (1)
    }

}
