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
 * An {@link java.util.Iterator Iterator} over an array of objects.
 * <p>
 * This iterator does not support {@link #remove}, as the object array cannot be
 * structurally modified.
 * <p>
 * The iterator implements a {@link #reset} method, allowing the reset of the iterator
 * back to the start if required.
 *
 * @param <E> the type to iterate over
 * @since 3.0
 */
public class ObjectArrayIterator<E> implements ResettableIterator<E> {

    /** The array */
    final E[] array;
    /** The start index to loop from */
    final int startIndex;
    /** The end index to loop to */
    final int endIndex;
    /** The current iterator index */
    int index = 0;

    //-------------------------------------------------------------------------
    /**
     * Constructs an ObjectArrayIterator that will iterate over the values in the
     * specified array.
     *
     * @param array the array to iterate over
     * @throws NullPointerException if <code>array</code> is <code>null</code>
     */
    public ObjectArrayIterator(final E... array) {
        this(array, 0, array.length);
    }

    /**
     * Constructs an ObjectArrayIterator that will iterate over the values in the
     * specified array from a specific start index.
     *
     * @param array  the array to iterate over
     * @param start  the index to start iterating at
     * @throws NullPointerException if <code>array</code> is <code>null</code>
     * @throws IndexOutOfBoundsException if the start index is out of bounds
     */
    public ObjectArrayIterator(final E array[], final int start) {
        this(array, start, array.length);
    }

    /**
     * Construct an ObjectArrayIterator that will iterate over a range of values
     * in the specified array.
     *
     * @param array  the array to iterate over
     * @param start  the index to start iterating at
     * @param end  the index (exclusive) to finish iterating at
     * @throws IndexOutOfBoundsException if the start or end index is out of bounds
     * @throws IllegalArgumentException if end index is before the start
     * @throws NullPointerException if <code>array</code> is <code>null</code>
     */
    public ObjectArrayIterator(final E array[], final int start, final int end) {
        super();
        if (start < 0) {
            throw new ArrayIndexOutOfBoundsException("Start index must not be less than zero");
        }
        if (end > array.length) {
            throw new ArrayIndexOutOfBoundsException("End index must not be greater than the array length");
        }
        if (start > array.length) {
            throw new ArrayIndexOutOfBoundsException("Start index must not be greater than the array length");
        }
        if (end < start) {
            throw new IllegalArgumentException("End index must not be less than start index");
        }
        this.array = array;
        this.startIndex = start;
        this.endIndex = end;
        this.index = start;
    }

    // Iterator interface
    //-------------------------------------------------------------------------

    /**
     * Returns true if there are more elements to return from the array.
     *
     * @return true if there is a next element to return
     */
    @Override
    public boolean hasNext() {
        return this.index < this.endIndex;
    }

    /**
     * Returns the next element in the array.
     *
     * @return the next element in the array
     * @throws NoSuchElementException if all the elements in the array
     *    have already been returned
     */
    @Override
    public E next() {
        if (hasNext() == false) {
            throw new NoSuchElementException();
        }
        return this.array[this.index++];
    }

    /**
     * Throws {@link UnsupportedOperationException}.
     *
     * @throws UnsupportedOperationException always
     */
    @Override
    public void remove() {
        throw new UnsupportedOperationException("remove() method is not supported for an ObjectArrayIterator");
    }

    // Properties
    //-------------------------------------------------------------------------

    /**
     * Gets the array that this iterator is iterating over.
     *
     * @return the array this iterator iterates over
     */
    public E[] getArray() {
        return this.array;
    }

    /**
     * Gets the start index to loop from.
     *
     * @return the start index
     */
    public int getStartIndex() {
        return this.startIndex;
    }

    /**
     * Gets the end index to loop to.
     *
     * @return the end index
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
