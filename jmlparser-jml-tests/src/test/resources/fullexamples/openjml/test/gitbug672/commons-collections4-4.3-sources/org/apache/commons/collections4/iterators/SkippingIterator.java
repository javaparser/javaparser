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

/**
 * Decorates another iterator to skip the first N elements.
 * <p>
 * In case an offset parameter other than 0 is provided, the decorated
 * iterator is immediately advanced to this position, skipping all elements
 * before that position.
 *
 * @since 4.1
 */
public class SkippingIterator<E> extends AbstractIteratorDecorator<E> {

    /** The offset to bound the first element return */
    private final long offset;

    /** The position of the current element */
    private long pos;

    //-----------------------------------------------------------------------

    /**
     * Decorates the specified iterator to skip all elements until the iterator
     * reaches the position at {@code offset}.
     * <p>
     * The iterator is immediately advanced until it reaches the position at {@code offset},
     * incurring O(n) time.
     *
     * @param iterator  the iterator to be decorated
     * @param offset  the index of the first element of the decorated iterator to return
     * @throws NullPointerException if iterator is null
     * @throws IllegalArgumentException if offset is negative
     */
    public SkippingIterator(final Iterator<E> iterator, final long offset) {
        super(iterator);

        if (offset < 0) {
            throw new IllegalArgumentException("Offset parameter must not be negative.");
        }

        this.offset = offset;
        this.pos = 0;
        init();
    }

    /**
     * Skips the given number of elements.
     */
    private void init() {
        while (pos < offset && hasNext()) {
            next();
        }
    }

    //-----------------------------------------------------------------------

    @Override
    public E next() {
        final E next = super.next();
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
        super.remove();
    }

}
