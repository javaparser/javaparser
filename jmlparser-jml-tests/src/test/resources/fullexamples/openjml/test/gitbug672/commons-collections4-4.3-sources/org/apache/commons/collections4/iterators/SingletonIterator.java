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

import java.util.NoSuchElementException;

import org.apache.commons.collections4.ResettableIterator;

/**
 * <code>SingletonIterator</code> is an {@link java.util.Iterator} over a single
 * object instance.
 *
 * @since 2.0
 */
public class SingletonIterator<E>
        implements ResettableIterator<E> {

    /** Whether remove is allowed */
    private final boolean removeAllowed;
    /** Is the cursor before the first element */
    private boolean beforeFirst = true;
    /** Has the element been removed */
    private boolean removed = false;
    /** The object */
    private E object;

    /**
     * Constructs a new <code>SingletonIterator</code> where <code>remove</code>
     * is a permitted operation.
     *
     * @param object  the single object to return from the iterator
     */
    public SingletonIterator(final E object) {
        this(object, true);
    }

    /**
     * Constructs a new <code>SingletonIterator</code> optionally choosing if
     * <code>remove</code> is a permitted operation.
     *
     * @param object  the single object to return from the iterator
     * @param removeAllowed  true if remove is allowed
     * @since 3.1
     */
    public SingletonIterator(final E object, final boolean removeAllowed) {
        super();
        this.object = object;
        this.removeAllowed = removeAllowed;
    }

    //-----------------------------------------------------------------------
    /**
     * Is another object available from the iterator?
     * <p>
     * This returns true if the single object hasn't been returned yet.
     *
     * @return true if the single object hasn't been returned yet
     */
    @Override
    public boolean hasNext() {
        return beforeFirst && !removed;
    }

    /**
     * Get the next object from the iterator.
     * <p>
     * This returns the single object if it hasn't been returned yet.
     *
     * @return the single object
     * @throws NoSuchElementException if the single object has already
     *    been returned
     */
    @Override
    public E next() {
        if (!beforeFirst || removed) {
            throw new NoSuchElementException();
        }
        beforeFirst = false;
        return object;
    }

    /**
     * Remove the object from this iterator.
     *
     * @throws IllegalStateException if the {@code next} method has not
     *        yet been called, or the {@code remove} method has already
     *        been called after the last call to the {@code next}
     *        method.
     * @throws UnsupportedOperationException if remove is not supported
     */
    @Override
    public void remove() {
        if (removeAllowed) {
            if (removed || beforeFirst) {
                throw new IllegalStateException();
            }
            object = null;
            removed = true;
        } else {
            throw new UnsupportedOperationException();
        }
    }

    /**
     * Reset the iterator to the start.
     */
    @Override
    public void reset() {
        beforeFirst = true;
    }

}
