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
package org.apache.commons.collections4.bag;

import java.util.Comparator;

import org.apache.commons.collections4.Bag;
import org.apache.commons.collections4.SortedBag;

/**
 * Decorates another {@link SortedBag} to synchronize its behaviour
 * for a multi-threaded environment.
 * <p>
 * Methods are synchronized, then forwarded to the decorated bag.
 * Iterators must be separately synchronized around the loop.
 * <p>
 * This class is Serializable from Commons Collections 3.1.
 *
 * @param <E> the type of elements in this bag
 * @since 3.0
 */
public class SynchronizedSortedBag<E> extends SynchronizedBag<E> implements SortedBag<E> {

    /** Serialization version */
    private static final long serialVersionUID = 722374056718497858L;

    /**
     * Factory method to create a synchronized sorted bag.
     *
     * @param <E> the type of the elements in the bag
     * @param bag  the bag to decorate, must not be null
     * @return a new synchronized SortedBag
     * @throws NullPointerException if bag is null
     * @since 4.0
     */
    public static <E> SynchronizedSortedBag<E> synchronizedSortedBag(final SortedBag<E> bag) {
        return new SynchronizedSortedBag<>(bag);
    }

    //-----------------------------------------------------------------------
    /**
     * Constructor that wraps (not copies).
     *
     * @param bag  the bag to decorate, must not be null
     * @throws NullPointerException if bag is null
     */
    protected SynchronizedSortedBag(final SortedBag<E> bag) {
        super(bag);
    }

    /**
     * Constructor that wraps (not copies).
     *
     * @param bag  the bag to decorate, must not be null
     * @param lock  the lock to use, must not be null
     * @throws NullPointerException if bag or lock is null
     */
    protected SynchronizedSortedBag(final Bag<E> bag, final Object lock) {
        super(bag, lock);
    }

    /**
     * Gets the bag being decorated.
     *
     * @return the decorated bag
     */
    protected SortedBag<E> getSortedBag() {
        return (SortedBag<E>) decorated();
    }

    //-----------------------------------------------------------------------

    @Override
    public synchronized E first() {
        synchronized (lock) {
            return getSortedBag().first();
        }
    }

    @Override
    public synchronized E last() {
        synchronized (lock) {
            return getSortedBag().last();
        }
    }

    @Override
    public synchronized Comparator<? super E> comparator() {
        synchronized (lock) {
            return getSortedBag().comparator();
        }
    }

}
