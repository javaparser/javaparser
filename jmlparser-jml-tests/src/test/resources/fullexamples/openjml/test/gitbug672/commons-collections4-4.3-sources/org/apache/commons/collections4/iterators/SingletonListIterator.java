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

import org.apache.commons.collections4.ResettableListIterator;

/**
 * <code>SingletonIterator</code> is an {@link java.util.ListIterator} over a single
 * object instance.
 *
 * @since 2.1
 */
public class SingletonListIterator<E> implements ResettableListIterator<E> {

    private boolean beforeFirst = true;
    private boolean nextCalled = false;
    private boolean removed = false;
    private E object;

    /**
     * Constructs a new <code>SingletonListIterator</code>.
     *
     * @param object  the single object to return from the iterator
     */
    public SingletonListIterator(final E object) {
        super();
        this.object = object;
    }

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
     * Is a previous object available from the iterator?
     * <p>
     * This returns true if the single object has been returned.
     *
     * @return true if the single object has been returned
     */
    @Override
    public boolean hasPrevious() {
        return !beforeFirst && !removed;
    }

    /**
     * Returns the index of the element that would be returned by a subsequent
     * call to {@code next}.
     *
     * @return 0 or 1 depending on current state.
     */
    @Override
    public int nextIndex() {
        return beforeFirst ? 0 : 1;
    }

    /**
     * Returns the index of the element that would be returned by a subsequent
     * call to {@code previous}. A return value of -1 indicates that the iterator is currently at
     * the start.
     *
     * @return 0 or -1 depending on current state.
     */
    @Override
    public int previousIndex() {
        return beforeFirst ? -1 : 0;
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
        nextCalled = true;
        return object;
    }

    /**
     * Get the previous object from the iterator.
     * <p>
     * This returns the single object if it has been returned.
     *
     * @return the single object
     * @throws NoSuchElementException if the single object has not already
     *    been returned
     */
    @Override
    public E previous() {
        if (beforeFirst || removed) {
            throw new NoSuchElementException();
        }
        beforeFirst = true;
        return object;
    }

    /**
     * Remove the object from this iterator.
     * @throws IllegalStateException if the {@code next} or {@code previous}
     *        method has not yet been called, or the {@code remove} method
     *        has already been called after the last call to {@code next}
     *        or {@code previous}.
     */
    @Override
    public void remove() {
        if(!nextCalled || removed) {
            throw new IllegalStateException();
        }
        object = null;
        removed = true;
    }

    /**
     * Add always throws {@link UnsupportedOperationException}.
     *
     * @param obj  the object to add
     * @throws UnsupportedOperationException always
     */
    @Override
    public void add(final E obj) {
        throw new UnsupportedOperationException("add() is not supported by this iterator");
    }

    /**
     * Set sets the value of the singleton.
     *
     * @param obj  the object to set
     * @throws IllegalStateException if {@code next} has not been called
     *          or the object has been removed
     */
    @Override
    public void set(final E obj) {
        if (!nextCalled || removed) {
            throw new IllegalStateException();
        }
        this.object = obj;
    }

    /**
     * Reset the iterator back to the start.
     */
    @Override
    public void reset() {
        beforeFirst = true;
        nextCalled = false;
    }

}
