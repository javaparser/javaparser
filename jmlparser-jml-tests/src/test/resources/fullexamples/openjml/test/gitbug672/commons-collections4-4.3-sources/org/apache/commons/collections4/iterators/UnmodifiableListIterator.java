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
package org.apache.commons.collections4.iterators;

import java.util.ListIterator;

import org.apache.commons.collections4.Unmodifiable;

/**
 * Decorates a list iterator such that it cannot be modified.
 * <p>
 * Attempts to modify it will result in an UnsupportedOperationException.
 *
 * @since 3.0
 */
public final class UnmodifiableListIterator<E> implements ListIterator<E>, Unmodifiable {

    /** The iterator being decorated */
    private final ListIterator<? extends E> iterator;

    //-----------------------------------------------------------------------
    /**
     * Decorates the specified iterator such that it cannot be modified.
     *
     * @param <E>  the element type
     * @param iterator  the iterator to decorate
     * @return a new unmodifiable list iterator
     * @throws NullPointerException if the iterator is null
     */
    public static <E> ListIterator<E> umodifiableListIterator(final ListIterator<? extends E> iterator) {
        if (iterator == null) {
            throw new NullPointerException("ListIterator must not be null");
        }
        if (iterator instanceof Unmodifiable) {
            @SuppressWarnings("unchecked") // safe to upcast
            final ListIterator<E> tmpIterator = (ListIterator<E>) iterator;
            return tmpIterator;
        }
        return new UnmodifiableListIterator<>(iterator);
    }

    //-----------------------------------------------------------------------
    /**
     * Constructor.
     *
     * @param iterator  the iterator to decorate
     */
    private UnmodifiableListIterator(final ListIterator<? extends E> iterator) {
        super();
        this.iterator = iterator;
    }

    //-----------------------------------------------------------------------
    @Override
    public boolean hasNext() {
        return iterator.hasNext();
    }

    @Override
    public E next() {
        return iterator.next();
    }

    @Override
    public int nextIndex() {
        return iterator.nextIndex();
    }

    @Override
    public boolean hasPrevious() {
        return iterator.hasPrevious();
    }

    @Override
    public E previous() {
        return iterator.previous();
    }

    @Override
    public int previousIndex() {
        return iterator.previousIndex();
    }

    @Override
    public void remove() {
        throw new UnsupportedOperationException("remove() is not supported");
    }

    @Override
    public void set(final E obj) {
        throw new UnsupportedOperationException("set() is not supported");
    }

    @Override
    public void add(final E obj) {
        throw new UnsupportedOperationException("add() is not supported");
    }

}
