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

import java.lang.reflect.Array;
import java.util.NoSuchElementException;

import org.apache.commons.collections4.ResettableIterator;

/**
 * Implements an {@link java.util.Iterator Iterator} over any array.
 * <p>
 * The array can be either an array of object or of primitives. If you know
 * that you have an object array, the
 * {@link org.apache.commons.collections4.iterators.ObjectArrayIterator ObjectArrayIterator}
 * class is a better choice, as it will perform better.
 * <p>
 * The iterator implements a {@link #reset} method, allowing the reset of
 * the iterator back to the start if required.
 *
 * @param <E> the type of elements returned by this iterator
 * @since 1.0
 */
public class ArrayIterator<E> implements ResettableIterator<E> {

    /** The array to iterate over */
    final Object array;
    /** The start index to loop from */
    final int startIndex;
    /** The end index to loop to */
    final int endIndex;
    /** The current iterator index */
    int index = 0;

    // Constructors
    // ----------------------------------------------------------------------
    /**
     * Constructs an ArrayIterator that will iterate over the values in the
     * specified array.
     *
     * @param array the array to iterate over.
     * @throws IllegalArgumentException if <code>array</code> is not an array.
     * @throws NullPointerException if <code>array</code> is <code>null</code>
     */
    public ArrayIterator(final Object array) {
        this(array, 0);
    }

    /**
     * Constructs an ArrayIterator that will iterate over the values in the
     * specified array from a specific start index.
     *
     * @param array  the array to iterate over.
     * @param startIndex  the index to start iterating at.
     * @throws IllegalArgumentException if <code>array</code> is not an array.
     * @throws NullPointerException if <code>array</code> is <code>null</code>
     * @throws IndexOutOfBoundsException if the index is invalid
     */
    public ArrayIterator(final Object array, final int startIndex) {
        this(array, startIndex, Array.getLength(array));
    }

    /**
     * Construct an ArrayIterator that will iterate over a range of values
     * in the specified array.
     *
     * @param array  the array to iterate over.
     * @param startIndex  the index to start iterating at.
     * @param endIndex  the index to finish iterating at.
     * @throws IllegalArgumentException if <code>array</code> is not an array.
     * @throws NullPointerException if <code>array</code> is <code>null</code>
     * @throws IndexOutOfBoundsException if either index is invalid
     */
    public ArrayIterator(final Object array, final int startIndex, final int endIndex) {
        super();

        this.array = array;
        this.startIndex = startIndex;
        this.endIndex = endIndex;
        this.index = startIndex;

        final int len = Array.getLength(array);
        checkBound(startIndex, len, "start");
        checkBound(endIndex, len, "end");
        if (endIndex < startIndex) {
            throw new IllegalArgumentException("End index must not be less than start index.");
        }
    }

    /**
     * Checks whether the index is valid or not.
     *
     * @param bound  the index to check
     * @param len  the length of the array
     * @param type  the index type (for error messages)
     * @throws IndexOutOfBoundsException if the index is invalid
     */
    protected void checkBound(final int bound, final int len, final String type ) {
        if (bound > len) {
            throw new ArrayIndexOutOfBoundsException(
              "Attempt to make an ArrayIterator that " + type +
              "s beyond the end of the array. "
            );
        }
        if (bound < 0) {
            throw new ArrayIndexOutOfBoundsException(
              "Attempt to make an ArrayIterator that " + type +
              "s before the start of the array. "
            );
        }
    }

    // Iterator interface
    //-----------------------------------------------------------------------
    /**
     * Returns true if there are more elements to return from the array.
     *
     * @return true if there is a next element to return
     */
    @Override
    public boolean hasNext() {
        return index < endIndex;
    }

    /**
     * Returns the next element in the array.
     *
     * @return the next element in the array
     * @throws NoSuchElementException if all the elements in the array
     *  have already been returned
     */
    @Override
    @SuppressWarnings("unchecked")
    public E next() {
        if (hasNext() == false) {
            throw new NoSuchElementException();
        }
        return (E) Array.get(array, index++);
    }

    /**
     * Throws {@link UnsupportedOperationException}.
     *
     * @throws UnsupportedOperationException always
     */
    @Override
    public void remove() {
        throw new UnsupportedOperationException("remove() method is not supported");
    }

    // Properties
    //-----------------------------------------------------------------------
    /**
     * Gets the array that this iterator is iterating over.
     *
     * @return the array this iterator iterates over.
     */
    public Object getArray() {
        return array;
    }

    /**
     * Gets the start index to loop from.
     *
     * @return the start index
     * @since 4.0
     */
    public int getStartIndex() {
        return this.startIndex;
    }

    /**
     * Gets the end index to loop to.
     *
     * @return the end index
     * @since 4.0
     */
    public int getEndIndex() {
        return this.endIndex;
    }

    /**
     * Resets the iterator back to the start index.
     */
    @Override
    public void reset() {
        this.index = this.startIndex;
    }

}
