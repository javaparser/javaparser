/*
 * Licensed to the Apache Software Foundation (ASF) under one or more
 * contributor license agreements. See the NOTICE file distributed with this
 * work for additional information regarding copyright ownership. The ASF
 * licenses this file to You under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 * http://www.apache.org/licenses/LICENSE-2.0 Unless required by applicable law
 * or agreed to in writing, software distributed under the License is
 * distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
 * KIND, either express or implied. See the License for the specific language
 * governing permissions and limitations under the License.
 */
package org.apache.commons.collections4.iterators;

import java.util.Iterator;
import java.util.NoSuchElementException;

/**
 * Decorates another iterator to return elements in a specific range.
 * <p>
 * The decorated iterator is bounded in the range [offset, offset+max).
 * The {@code offset} corresponds to the position of the first element to
 * be returned from the decorated iterator, and {@code max} is the maximum
 * number of elements to be returned at most.
 * <p>
 * In case an offset parameter other than 0 is provided, the decorated
 * iterator is immediately advanced to this position, skipping all elements
 * before that position.
 *
 * @since 4.1
 */
public class BoundedIterator<E> implements Iterator<E> {

    /** The iterator being decorated. */
    private final Iterator<? extends E> iterator;

    /** The offset to bound the first element return */
    private final long offset;

    /** The max number of elements to return */
    private final long max;

    /** The position of the current element */
    private long pos;

    //-----------------------------------------------------------------------

    /**
     * Decorates the specified iterator to return at most the given number of elements,
     * skipping all elements until the iterator reaches the position at {@code offset}.
     * <p>
     * The iterator is immediately advanced until it reaches the position at {@code offset},
     * incurring O(n) time.
     *
     * @param iterator  the iterator to be decorated
     * @param offset  the index of the first element of the decorated iterator to return
     * @param max  the maximum number of elements of the decorated iterator to return
     * @throws NullPointerException if iterator is null
     * @throws IllegalArgumentException if either offset or max is negative
     */
    public BoundedIterator(final Iterator<? extends E> iterator, final long offset, final long max) {
        if (iterator == null) {
            throw new NullPointerException("Iterator must not be null");
        }
        if (offset < 0) {
            throw new IllegalArgumentException("Offset parameter must not be negative.");
        }
        if (max < 0) {
            throw new IllegalArgumentException("Max parameter must not be negative.");
        }

        this.iterator = iterator;
        this.offset = offset;
        this.max = max;
        pos = 0;
        init();
    }

    /**
     * Advances the underlying iterator to the beginning of the bounded range.
     */
    private void init() {
        while (pos < offset && iterator.hasNext()) {
            iterator.next();
            pos++;
        }
    }

    //-----------------------------------------------------------------------

    @Override
    public boolean hasNext() {
        if (!checkBounds()) {
            return false;
        }
        return iterator.hasNext();
    }

    /**
     * Checks whether the iterator is still within its bounded range.
     * @return {@code true} if the iterator is within its bounds, {@code false} otherwise
     */
    private boolean checkBounds() {
        if (pos - offset + 1 > max) {
            return false;
        }
        return true;
    }

    @Override
    public E next() {
        if (!checkBounds()) {
            throw new NoSuchElementException();
        }
        final E next = iterator.next();
        pos++;
        return next;
    }

    /**
     * {@inheritDoc}
     * <p>
     * In case an offset other than 0 was specified, the underlying iterator will be advanced
     * to this position upon creation. A call to {@link #remove()} will still result in an
     * {@link IllegalStateException} if no explicit call to {@link #next()} has been made prior
     * to calling {@link #remove()}.
     */
    @Override
    public void remove() {
        if (pos <= offset) {
            throw new IllegalStateException("remove() can not be called before calling next()");
        }
        iterator.remove();
    }
}
