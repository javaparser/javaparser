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

import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Queue;

/**
 * An IteratorChain is an Iterator that wraps a number of Iterators.
 * <p>
 * This class makes multiple iterators look like one to the caller. When any
 * method from the Iterator interface is called, the IteratorChain will delegate
 * to a single underlying Iterator. The IteratorChain will invoke the Iterators
 * in sequence until all Iterators are exhausted.
 * <p>
 * Under many circumstances, linking Iterators together in this manner is more
 * efficient (and convenient) than reading out the contents of each Iterator
 * into a List and creating a new Iterator.
 * <p>
 * Calling a method that adds new Iterator <i>after a method in the Iterator
 * interface has been called</i> will result in an UnsupportedOperationException.
 * <p>
 * NOTE: As from version 3.0, the IteratorChain may contain no iterators. In
 * this case the class will function as an empty iterator.
 * <p>
 * NOTE: As from version 4.0, the IteratorChain stores the iterators in a queue
 * and removes any reference to them as soon as they are not used anymore. Thus
 * the methods {@code setIterator(Iterator)} and {@code getIterators()} have been
 * removed and {@link #size()} will return the number of remaining iterators in
 * the queue.
 *
 * @since 2.1
 */
public class IteratorChain<E> implements Iterator<E> {

    /** The chain of iterators */
    private final Queue<Iterator<? extends E>> iteratorChain = new LinkedList<>();

    /** The current iterator */
    private Iterator<? extends E> currentIterator = null;

    /**
     * The "last used" Iterator is the Iterator upon which next() or hasNext()
     * was most recently called used for the remove() operation only
     */
    private Iterator<? extends E> lastUsedIterator = null;

    /**
     * ComparatorChain is "locked" after the first time compare(Object,Object)
     * is called
     */
    private boolean isLocked = false;

    //-----------------------------------------------------------------------
    /**
     * Construct an IteratorChain with no Iterators.
     * <p>
     * You will normally use {@link #addIterator(Iterator)} to add some
     * iterators after using this constructor.
     */
    public IteratorChain() {
        super();
    }

    /**
     * Construct an IteratorChain with a single Iterator.
     * <p>
     * This method takes one iterator. The newly constructed iterator will
     * iterate through that iterator. Thus calling this constructor on its own
     * will have no effect other than decorating the input iterator.
     * <p>
     * You will normally use {@link #addIterator(Iterator)} to add some more
     * iterators after using this constructor.
     *
     * @param iterator the first child iterator in the IteratorChain, not null
     * @throws NullPointerException if the iterator is null
     */
    public IteratorChain(final Iterator<? extends E> iterator) {
        super();
        addIterator(iterator);
    }

    /**
     * Constructs a new <code>IteratorChain</code> over the two given iterators.
     * <p>
     * This method takes two iterators. The newly constructed iterator will
     * iterate through each one of the input iterators in turn.
     *
     * @param first the first child iterator in the IteratorChain, not null
     * @param second the second child iterator in the IteratorChain, not null
     * @throws NullPointerException if either iterator is null
     */
    public IteratorChain(final Iterator<? extends E> first, final Iterator<? extends E> second) {
        super();
        addIterator(first);
        addIterator(second);
    }

    /**
     * Constructs a new <code>IteratorChain</code> over the array of iterators.
     * <p>
     * This method takes an array of iterators. The newly constructed iterator
     * will iterate through each one of the input iterators in turn.
     *
     * @param iteratorChain the array of iterators, not null
     * @throws NullPointerException if iterators array is or contains null
     */
    public IteratorChain(final Iterator<? extends E>... iteratorChain) {
        super();
        for (final Iterator<? extends E> element : iteratorChain) {
            addIterator(element);
        }
    }

    /**
     * Constructs a new <code>IteratorChain</code> over the collection of
     * iterators.
     * <p>
     * This method takes a collection of iterators. The newly constructed
     * iterator will iterate through each one of the input iterators in turn.
     *
     * @param iteratorChain the collection of iterators, not null
     * @throws NullPointerException if iterators collection is or contains null
     * @throws ClassCastException if iterators collection doesn't contain an
     * iterator
     */
    public IteratorChain(final Collection<Iterator<? extends E>> iteratorChain) {
        super();
        for (final Iterator<? extends E> iterator : iteratorChain) {
            addIterator(iterator);
        }
    }

    //-----------------------------------------------------------------------
    /**
     * Add an Iterator to the end of the chain
     *
     * @param iterator Iterator to add
     * @throws IllegalStateException if I've already started iterating
     * @throws NullPointerException if the iterator is null
     */
    public void addIterator(final Iterator<? extends E> iterator) {
        checkLocked();
        if (iterator == null) {
            throw new NullPointerException("Iterator must not be null");
        }
        iteratorChain.add(iterator);
    }

    /**
     * Returns the remaining number of Iterators in the current IteratorChain.
     *
     * @return Iterator count
     */
    public int size() {
        return iteratorChain.size();
    }

    /**
     * Determine if modifications can still be made to the IteratorChain.
     * IteratorChains cannot be modified once they have executed a method from
     * the Iterator interface.
     *
     * @return true if IteratorChain cannot be modified, false if it can
     */
    public boolean isLocked() {
        return isLocked;
    }

    /**
     * Checks whether the iterator chain is now locked and in use.
     */
    private void checkLocked() {
        if (isLocked == true) {
            throw new UnsupportedOperationException(
                    "IteratorChain cannot be changed after the first use of a method from the Iterator interface");
        }
    }

    /**
     * Lock the chain so no more iterators can be added. This must be called
     * from all Iterator interface methods.
     */
    private void lockChain() {
        if (isLocked == false) {
            isLocked = true;
        }
    }

    /**
     * Updates the current iterator field to ensure that the current Iterator is
     * not exhausted
     */
    protected void updateCurrentIterator() {
        if (currentIterator == null) {
            if (iteratorChain.isEmpty()) {
                currentIterator = EmptyIterator.<E> emptyIterator();
            } else {
                currentIterator = iteratorChain.remove();
            }
            // set last used iterator here, in case the user calls remove
            // before calling hasNext() or next() (although they shouldn't)
            lastUsedIterator = currentIterator;
        }

        while (currentIterator.hasNext() == false && !iteratorChain.isEmpty()) {
            currentIterator = iteratorChain.remove();
        }
    }

    //-----------------------------------------------------------------------
    /**
     * Return true if any Iterator in the IteratorChain has a remaining element.
     *
     * @return true if elements remain
     */
    @Override
    public boolean hasNext() {
        lockChain();
        updateCurrentIterator();
        lastUsedIterator = currentIterator;

        return currentIterator.hasNext();
    }

    /**
     * Returns the next Object of the current Iterator
     *
     * @return Object from the current Iterator
     * @throws java.util.NoSuchElementException if all the Iterators are
     * exhausted
     */
    @Override
    public E next() {
        lockChain();
        updateCurrentIterator();
        lastUsedIterator = currentIterator;

        return currentIterator.next();
    }

    /**
     * Removes from the underlying collection the last element returned by the
     * Iterator. As with next() and hasNext(), this method calls remove() on the
     * underlying Iterator. Therefore, this method may throw an
     * UnsupportedOperationException if the underlying Iterator does not support
     * this method.
     *
     * @throws UnsupportedOperationException if the remove operator is not
     * supported by the underlying Iterator
     * @throws IllegalStateException if the next method has not yet been called,
     * or the remove method has already been called after the last call to the
     * next method.
     */
    @Override
    public void remove() {
        lockChain();
        if (currentIterator == null) {
            updateCurrentIterator();
        }
        lastUsedIterator.remove();
    }

}
