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

import java.util.Iterator;

import org.apache.commons.collections4.Unmodifiable;

/**
 * Decorates an iterator such that it cannot be modified.
 * <p>
 * Attempts to modify it will result in an UnsupportedOperationException.
 *
 * @since 3.0
 */
public final class UnmodifiableIterator<E> implements Iterator<E>, Unmodifiable {

    /** The iterator being decorated */
    private final Iterator<? extends E> iterator;

    //-----------------------------------------------------------------------
    /**
     * Decorates the specified iterator such that it cannot be modified.
     * <p>
     * If the iterator is already unmodifiable it is returned directly.
     *
     * @param <E>  the element type
     * @param iterator  the iterator to decorate
     * @return a new unmodifiable iterator
     * @throws NullPointerException if the iterator is null
     */
    public static <E> Iterator<E> unmodifiableIterator(final Iterator<? extends E> iterator) {
        if (iterator == null) {
            throw new NullPointerException("Iterator must not be null");
        }
        if (iterator instanceof Unmodifiable) {
            @SuppressWarnings("unchecked") // safe to upcast
            final Iterator<E> tmpIterator = (Iterator<E>) iterator;
            return tmpIterator;
        }
        return new UnmodifiableIterator<>(iterator);
    }

    //-----------------------------------------------------------------------
    /**
     * Constructor.
     *
     * @param iterator  the iterator to decorate
     */
    private UnmodifiableIterator(final Iterator<? extends E> iterator) {
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
    public void remove() {
        throw new UnsupportedOperationException("remove() is not supported");
    }

}
