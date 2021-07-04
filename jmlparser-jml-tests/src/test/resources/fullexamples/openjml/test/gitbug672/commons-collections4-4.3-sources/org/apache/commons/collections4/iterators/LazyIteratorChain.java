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

import java.util.Iterator;

/**
 * An LazyIteratorChain is an Iterator that wraps a number of Iterators in a lazy manner.
 * <p>
 * This class makes multiple iterators look like one to the caller. When any
 * method from the Iterator interface is called, the LazyIteratorChain will delegate
 * to a single underlying Iterator. The LazyIteratorChain will invoke the Iterators
 * in sequence until all Iterators are exhausted.
 * <p>
 * The Iterators are provided by {@link #nextIterator(int)} which has to be overridden by
 * sub-classes and allows to lazily create the Iterators as they are accessed:
 * <pre>
 * return new LazyIteratorChain&lt;String&gt;() {
 *     protected Iterator&lt;String&gt; nextIterator(int count) {
 *         return count == 1 ? Arrays.asList("foo", "bar").iterator() : null;
 *     }
 * };
 * </pre>
 * <p>
 * Once the inner Iterator's {@link Iterator#hasNext()} method returns false,
 * {@link #nextIterator(int)} will be called to obtain another iterator, and so on
 * until {@link #nextIterator(int)} returns null, indicating that the chain is exhausted.
 * <p>
 * NOTE: The LazyIteratorChain may contain no iterators. In this case the class will
 * function as an empty iterator.
 *
 * @since 4.0
 */
public abstract class LazyIteratorChain<E> implements Iterator<E> {

    /** The number of times {@link #next()} was already called. */
    private int callCounter = 0;

    /** Indicates that the Iterator chain has been exhausted. */
    private boolean chainExhausted = false;

    /** The current iterator. */
    private Iterator<? extends E> currentIterator = null;

    /**
     * The "last used" Iterator is the Iterator upon which next() or hasNext()
     * was most recently called used for the remove() operation only.
     */
    private Iterator<? extends E> lastUsedIterator = null;

    //-----------------------------------------------------------------------

    /**
     * Gets the next iterator after the previous one has been exhausted.
     * <p>
     * This method <b>MUST</b> return null when there are no more iterators.
     *
     * @param count the number of time this method has been called (starts with 1)
     * @return the next iterator, or null if there are no more.
     */
    protected abstract Iterator<? extends E> nextIterator(int count);

    /**
     * Updates the current iterator field to ensure that the current Iterator
     * is not exhausted.
     */
    private void updateCurrentIterator() {
        if (callCounter == 0) {
            currentIterator = nextIterator(++callCounter);
            if (currentIterator == null) {
                currentIterator = EmptyIterator.<E>emptyIterator();
                chainExhausted = true;
            }
            // set last used iterator here, in case the user calls remove
            // before calling hasNext() or next() (although they shouldn't)
            lastUsedIterator = currentIterator;
        }

        while (currentIterator.hasNext() == false && !chainExhausted) {
            final Iterator<? extends E> nextIterator = nextIterator(++callCounter);
            if (nextIterator != null) {
                currentIterator = nextIterator;
            } else {
                chainExhausted = true;
            }
        }
    }

    //-----------------------------------------------------------------------

    /**
     * Return true if any Iterator in the chain has a remaining element.
     *
     * @return true if elements remain
     */
    @Override
    public boolean hasNext() {
        updateCurrentIterator();
        lastUsedIterator = currentIterator;

        return currentIterator.hasNext();
    }

    /**
     * Returns the next element of the current Iterator
     *
     * @return element from the current Iterator
     * @throws java.util.NoSuchElementException if all the Iterators are exhausted
     */
    @Override
    public E next() {
        updateCurrentIterator();
        lastUsedIterator = currentIterator;

        return currentIterator.next();
    }

    /**
     * Removes from the underlying collection the last element returned by the Iterator.
     * <p>
     * As with next() and hasNext(), this method calls remove() on the underlying Iterator.
     * Therefore, this method may throw an UnsupportedOperationException if the underlying
     * Iterator does not support this method.
     *
     * @throws UnsupportedOperationException if the remove operator is not
     *   supported by the underlying Iterator
     * @throws IllegalStateException if the next method has not yet been called,
     *   or the remove method has already been called after the last call to the next method.
     */
    @Override
    public void remove() {
        if (currentIterator == null) {
            updateCurrentIterator();
        }
        lastUsedIterator.remove();
    }

}
