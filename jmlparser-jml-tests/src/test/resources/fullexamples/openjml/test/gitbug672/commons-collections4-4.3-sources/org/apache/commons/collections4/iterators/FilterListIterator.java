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
import java.util.NoSuchElementException;

import org.apache.commons.collections4.Predicate;

/**
 * Decorates another {@link ListIterator} using a predicate to filter elements.
 * <p>
 * This iterator decorates the underlying iterator, only allowing through
 * those elements that match the specified {@link Predicate Predicate}.
 *
 * @since 2.0
 */
public class FilterListIterator<E> implements ListIterator<E> {

    /** The iterator being used */
    private ListIterator<? extends E> iterator;

    /** The predicate being used */
    private Predicate<? super E> predicate;

    /**
     * The value of the next (matching) object, when
     * {@link #nextObjectSet} is true.
     */
    private E nextObject;

    /**
     * Whether or not the {@link #nextObject} has been set
     * (possibly to <code>null</code>).
     */
    private boolean nextObjectSet = false;

    /**
     * The value of the previous (matching) object, when
     * {@link #previousObjectSet} is true.
     */
    private E previousObject;

    /**
     * Whether or not the {@link #previousObject} has been set
     * (possibly to <code>null</code>).
     */
    private boolean previousObjectSet = false;

    /**
     * The index of the element that would be returned by {@link #next}.
     */
    private int nextIndex = 0;

    //-----------------------------------------------------------------------
    /**
     * Constructs a new <code>FilterListIterator</code> that will not function
     * until {@link #setListIterator(ListIterator) setListIterator}
     * and {@link #setPredicate(Predicate) setPredicate} are invoked.
     */
    public FilterListIterator() {
        super();
    }

    /**
     * Constructs a new <code>FilterListIterator</code> that will not
     * function until {@link #setPredicate(Predicate) setPredicate} is invoked.
     *
     * @param iterator  the iterator to use
     */
    public FilterListIterator(final ListIterator<? extends E> iterator ) {
        super();
        this.iterator = iterator;
    }

    /**
     * Constructs a new <code>FilterListIterator</code>.
     *
     * @param iterator  the iterator to use
     * @param predicate  the predicate to use
     */
    public FilterListIterator(final ListIterator<? extends E> iterator, final Predicate<? super E> predicate) {
        super();
        this.iterator = iterator;
        this.predicate = predicate;
    }

    /**
     * Constructs a new <code>FilterListIterator</code> that will not function
     * until {@link #setListIterator(ListIterator) setListIterator} is invoked.
     *
     * @param predicate  the predicate to use.
     */
    public FilterListIterator(final Predicate<? super E> predicate) {
        super();
        this.predicate = predicate;
    }

    //-----------------------------------------------------------------------
    /**
     * Not supported.
     * @param o the element to insert
     */
    @Override
    public void add(final E o) {
        throw new UnsupportedOperationException("FilterListIterator.add(Object) is not supported.");
    }

    @Override
    public boolean hasNext() {
        return nextObjectSet || setNextObject();
    }

    @Override
    public boolean hasPrevious() {
        return previousObjectSet || setPreviousObject();
    }

    @Override
    public E next() {
        if (!nextObjectSet && !setNextObject()) {
            throw new NoSuchElementException();
        }
        nextIndex++;
        final E temp = nextObject;
        clearNextObject();
        return temp;
    }

    @Override
    public int nextIndex() {
        return nextIndex;
    }

    @Override
    public E previous() {
        if (!previousObjectSet && !setPreviousObject()) {
            throw new NoSuchElementException();
        }
        nextIndex--;
        final E temp = previousObject;
        clearPreviousObject();
        return temp;
    }

    @Override
    public int previousIndex() {
        return nextIndex-1;
    }

    /** Not supported. */
    @Override
    public void remove() {
        throw new UnsupportedOperationException("FilterListIterator.remove() is not supported.");
    }

    /**
     * Not supported.
     * @param o the element with which to replace the last element returned by
     *          {@code next} or {@code previous}
     */
    @Override
    public void set(final E o) {
        throw new UnsupportedOperationException("FilterListIterator.set(Object) is not supported.");
    }

    //-----------------------------------------------------------------------
    /**
     * Gets the iterator this iterator is using.
     *
     * @return the iterator.
     */
    public ListIterator<? extends E> getListIterator() {
        return iterator;
    }

    /**
     * Sets the iterator for this iterator to use.
     * If iteration has started, this effectively resets the iterator.
     *
     * @param iterator  the iterator to use
     */
    public void setListIterator(final ListIterator<? extends E> iterator) {
        this.iterator = iterator;
    }

    //-----------------------------------------------------------------------
    /**
     * Gets the predicate this iterator is using.
     *
     * @return the predicate.
     */
    public Predicate<? super E> getPredicate() {
        return predicate;
    }

    /**
     * Sets the predicate this the iterator to use.
     *
     * @param predicate  the transformer to use
     */
    public void setPredicate(final Predicate<? super E> predicate) {
        this.predicate = predicate;
    }

    //-----------------------------------------------------------------------
    private void clearNextObject() {
        nextObject = null;
        nextObjectSet = false;
    }

    private boolean setNextObject() {
        // if previousObjectSet,
        // then we've walked back one step in the
        // underlying list (due to a hasPrevious() call)
        // so skip ahead one matching object
        if (previousObjectSet) {
            clearPreviousObject();
            if (!setNextObject()) {
                return false;
            }
            clearNextObject();
        }

        if (iterator == null) {
            return false;
        }
        while (iterator.hasNext()) {
            final E object = iterator.next();
            if (predicate.evaluate(object)) {
                nextObject = object;
                nextObjectSet = true;
                return true;
            }
        }
        return false;
    }

    private void clearPreviousObject() {
        previousObject = null;
        previousObjectSet = false;
    }

    private boolean setPreviousObject() {
        // if nextObjectSet,
        // then we've walked back one step in the
        // underlying list (due to a hasNext() call)
        // so skip ahead one matching object
        if (nextObjectSet) {
            clearNextObject();
            if (!setPreviousObject()) {
                return false;
            }
            clearPreviousObject();
        }

        if (iterator == null) {
            return false;
        }
        while (iterator.hasPrevious()) {
            final E object = iterator.previous();
            if (predicate.evaluate(object)) {
                previousObject = object;
                previousObjectSet = true;
                return true;
            }
        }
        return false;
    }

}
