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

import java.util.Enumeration;
import java.util.Iterator;

/**
 * Adapter to make an {@link Iterator Iterator} instance appear to be an
 * {@link Enumeration Enumeration} instance.
 *
 * @since 1.0
 */
public class IteratorEnumeration<E> implements Enumeration<E> {

    /** The iterator being decorated. */
    private Iterator<? extends E> iterator;

    /**
     * Constructs a new <code>IteratorEnumeration</code> that will not function
     * until {@link #setIterator(Iterator) setIterator} is invoked.
     */
    public IteratorEnumeration() {
    }

    /**
     * Constructs a new <code>IteratorEnumeration</code> that will use the given
     * iterator.
     *
     * @param iterator the iterator to use
     */
    public IteratorEnumeration(final Iterator<? extends E> iterator) {
        this.iterator = iterator;
    }

    // Iterator interface
    //-------------------------------------------------------------------------

    /**
     * Returns true if the underlying iterator has more elements.
     *
     * @return true if the underlying iterator has more elements
     */
    @Override
    public boolean hasMoreElements() {
        return iterator.hasNext();
    }

    /**
     * Returns the next element from the underlying iterator.
     *
     * @return the next element from the underlying iterator.
     * @throws java.util.NoSuchElementException if the underlying iterator has
     * no more elements
     */
    @Override
    public E nextElement() {
        return iterator.next();
    }

    // Properties
    //-------------------------------------------------------------------------

    /**
     * Returns the underlying iterator.
     *
     * @return the underlying iterator
     */
    public Iterator<? extends E> getIterator() {
        return iterator;
    }

    /**
     * Sets the underlying iterator.
     *
     * @param iterator the new underlying iterator
     */
    public void setIterator(final Iterator<? extends E> iterator) {
        this.iterator = iterator;
    }

}
