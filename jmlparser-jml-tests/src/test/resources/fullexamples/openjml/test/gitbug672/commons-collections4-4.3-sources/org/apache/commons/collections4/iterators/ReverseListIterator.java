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

import java.util.List;
import java.util.ListIterator;

import org.apache.commons.collections4.ResettableListIterator;

/**
 * Iterates backwards through a List, starting with the last element
 * and continuing to the first. This is useful for looping around
 * a list in reverse order without needing to actually reverse the list.
 * <p>
 * The first call to <code>next()</code> will return the last element
 * from the list, and so on. The <code>hasNext()</code> method works
 * in concert with the <code>next()</code> method as expected.
 * However, the <code>nextIndex()</code> method returns the correct
 * index in the list, thus it starts high and reduces as the iteration
 * continues. The previous methods work similarly.
 *
 * @since 3.2
 */
public class ReverseListIterator<E> implements ResettableListIterator<E> {

    /** The list being wrapped. */
    private final List<E> list;
    /** The list iterator being wrapped. */
    private ListIterator<E> iterator;
    /** Flag to indicate if updating is possible at the moment. */
    private boolean validForUpdate = true;

    /**
     * Constructor that wraps a list.
     *
     * @param list  the list to create a reversed iterator for
     * @throws NullPointerException if the list is null
     */
    public ReverseListIterator(final List<E> list) {
        super();
        if (list == null) {
            throw new NullPointerException("List must not be null.");
        }
        this.list = list;
        iterator = list.listIterator(list.size());
    }

    //-----------------------------------------------------------------------
    /**
     * Checks whether there is another element.
     *
     * @return true if there is another element
     */
    @Override
    public boolean hasNext() {
        return iterator.hasPrevious();
    }

    /**
     * Gets the next element.
     * The next element is the previous in the list.
     *
     * @return the next element in the iterator
     */
    @Override
    public E next() {
        final E obj = iterator.previous();
        validForUpdate = true;
        return obj;
    }

    /**
     * Gets the index of the next element.
     *
     * @return the index of the next element in the iterator
     */
    @Override
    public int nextIndex() {
        return iterator.previousIndex();
    }

    /**
     * Checks whether there is a previous element.
     *
     * @return true if there is a previous element
     */
    @Override
    public boolean hasPrevious() {
        return iterator.hasNext();
    }

    /**
     * Gets the previous element.
     * The next element is the previous in the list.
     *
     * @return the previous element in the iterator
     */
    @Override
    public E previous() {
        final E obj = iterator.next();
        validForUpdate = true;
        return obj;
    }

    /**
     * Gets the index of the previous element.
     *
     * @return the index of the previous element in the iterator
     */
    @Override
    public int previousIndex() {
        return iterator.nextIndex();
    }

    /**
     * Removes the last returned element.
     *
     * @throws UnsupportedOperationException if the list is unmodifiable
     * @throws IllegalStateException if there is no element to remove
     */
    @Override
    public void remove() {
        if (validForUpdate == false) {
            throw new IllegalStateException("Cannot remove from list until next() or previous() called");
        }
        iterator.remove();
    }

    /**
     * Replaces the last returned element.
     *
     * @param obj  the object to set
     * @throws UnsupportedOperationException if the list is unmodifiable
     * @throws IllegalStateException if the iterator is not in a valid state for set
     */
    @Override
    public void set(final E obj) {
        if (validForUpdate == false) {
            throw new IllegalStateException("Cannot set to list until next() or previous() called");
        }
        iterator.set(obj);
    }

    /**
     * Adds a new element to the list between the next and previous elements.
     *
     * @param obj  the object to add
     * @throws UnsupportedOperationException if the list is unmodifiable
     * @throws IllegalStateException if the iterator is not in a valid state for set
     */
    @Override
    public void add(final E obj) {
        // the validForUpdate flag is needed as the necessary previous()
        // method call re-enables remove and add
        if (validForUpdate == false) {
            throw new IllegalStateException("Cannot add to list until next() or previous() called");
        }
        validForUpdate = false;
        iterator.add(obj);
        iterator.previous();
    }

    /**
     * Resets the iterator back to the start (which is the
     * end of the list as this is a reversed iterator)
     */
    @Override
    public void reset() {
        iterator = list.listIterator(list.size());
    }

}
