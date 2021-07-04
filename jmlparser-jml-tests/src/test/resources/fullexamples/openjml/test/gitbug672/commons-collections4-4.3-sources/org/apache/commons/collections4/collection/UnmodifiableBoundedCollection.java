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
package org.apache.commons.collections4.collection;

import java.util.Collection;
import java.util.Iterator;

import org.apache.commons.collections4.BoundedCollection;
import org.apache.commons.collections4.Unmodifiable;
import org.apache.commons.collections4.iterators.UnmodifiableIterator;

/**
 * {@link UnmodifiableBoundedCollection} decorates another
 * {@link BoundedCollection} to ensure it can't be altered.
 * <p>
 * If a BoundedCollection is first wrapped in some other collection decorator,
 * such as synchronized or predicated, the BoundedCollection methods are no
 * longer accessible.
 * The factory on this class will attempt to retrieve the bounded nature by
 * examining the package scope variables.
 * <p>
 * This class is Serializable from Commons Collections 3.1.
 * <p>
 * Attempts to modify it will result in an UnsupportedOperationException.
 *
 * @param <E> the type of elements in this collection
 * @since 3.0
 */
public final class UnmodifiableBoundedCollection<E> extends AbstractCollectionDecorator<E>
        implements BoundedCollection<E>, Unmodifiable {

    /** Serialization version */
    private static final long serialVersionUID = -7112672385450340330L;

    /**
     * Factory method to create an unmodifiable bounded collection.
     *
     * @param <E> the type of the elements in the collection
     * @param coll  the <code>BoundedCollection</code> to decorate, must not be null
     * @return a new unmodifiable bounded collection
     * @throws NullPointerException if {@code coll} is {@code null}
     * @since 4.0
     */
    public static <E> BoundedCollection<E> unmodifiableBoundedCollection(final BoundedCollection<? extends E> coll) {
        if (coll instanceof Unmodifiable) {
            @SuppressWarnings("unchecked") // safe to upcast
            final BoundedCollection<E> tmpColl = (BoundedCollection<E>) coll;
            return tmpColl;
        }
        return new UnmodifiableBoundedCollection<>(coll);
    }

    /**
     * Factory method to create an unmodifiable bounded collection.
     * <p>
     * This method is capable of drilling down through up to 1000 other decorators
     * to find a suitable BoundedCollection.
     *
     * @param <E> the type of the elements in the collection
     * @param coll  the <code>BoundedCollection</code> to decorate, must not be null
     * @return a new unmodifiable bounded collection
     * @throws NullPointerException if coll is null
     * @throws IllegalArgumentException if coll is not a {@code BoundedCollection}
     * @since 4.0
     */
    @SuppressWarnings("unchecked")
    public static <E> BoundedCollection<E> unmodifiableBoundedCollection(Collection<? extends E> coll) {
        if (coll == null) {
            throw new NullPointerException("Collection must not be null.");
        }

        // handle decorators
        for (int i = 0; i < 1000; i++) {  // counter to prevent infinite looping
            if (coll instanceof BoundedCollection) {
                break;  // normal loop exit
            }
            if (coll instanceof AbstractCollectionDecorator) {
                coll = ((AbstractCollectionDecorator<E>) coll).decorated();
            } else if (coll instanceof SynchronizedCollection) {
                coll = ((SynchronizedCollection<E>) coll).decorated();
            }
        }

        if (coll instanceof BoundedCollection == false) {
            throw new IllegalArgumentException("Collection is not a bounded collection.");
        }
        return new UnmodifiableBoundedCollection<>((BoundedCollection<E>) coll);
    }

    /**
     * Constructor that wraps (not copies).
     *
     * @param coll  the collection to decorate, must not be null
     * @throws NullPointerException if coll is null
     */
    @SuppressWarnings("unchecked") // safe to upcast
    private UnmodifiableBoundedCollection(final BoundedCollection<? extends E> coll) {
        super((BoundedCollection<E>) coll);
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

    //-----------------------------------------------------------------------
    @Override
    public boolean isFull() {
        return decorated().isFull();
    }

    @Override
    public int maxSize() {
        return decorated().maxSize();
    }

    @Override
    protected BoundedCollection<E> decorated() {
        return (BoundedCollection<E>) super.decorated();
    }
}
