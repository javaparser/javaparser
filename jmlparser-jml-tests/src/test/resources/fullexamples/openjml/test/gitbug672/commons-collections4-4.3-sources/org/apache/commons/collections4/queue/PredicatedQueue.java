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
package org.apache.commons.collections4.queue;

import java.util.Queue;

import org.apache.commons.collections4.Predicate;
import org.apache.commons.collections4.collection.PredicatedCollection;

/**
 * Decorates another {@link Queue} to validate that additions
 * match a specified predicate.
 * <p>
 * This queue exists to provide validation for the decorated queue.
 * It is normally created to decorate an empty queue.
 * If an object cannot be added to the queue, an IllegalArgumentException is thrown.
 * <p>
 * One usage would be to ensure that no null entries are added to the queue.
 * <pre>Queue queue = PredicatedQueue.predicatedQueue(new UnboundedFifoQueue(), NotNullPredicate.INSTANCE);</pre>
 *
 * @param <E> the type of elements held in this queue
 * @since 4.0
 */
public class PredicatedQueue<E> extends PredicatedCollection<E> implements Queue<E> {

    /** Serialization version */
    private static final long serialVersionUID = 2307609000539943581L;

    /**
     * Factory method to create a predicated (validating) queue.
     * <p>
     * If there are any elements already in the queue being decorated, they
     * are validated.
     *
     * @param <E> the type of the elements in the queue
     * @param Queue  the queue to decorate, must not be null
     * @param predicate  the predicate to use for validation, must not be null
     * @return a new predicated queue
     * @throws NullPointerException if queue or predicate is null
     * @throws IllegalArgumentException if the queue contains invalid elements
     */
    public static <E> PredicatedQueue<E> predicatedQueue(final Queue<E> Queue,
                                                          final Predicate<? super E> predicate) {
        return new PredicatedQueue<>(Queue, predicate);
    }

    //-----------------------------------------------------------------------
    /**
     * Constructor that wraps (not copies).
     * <p>
     * If there are any elements already in the collection being decorated, they
     * are validated.
     *
     * @param queue  the queue to decorate, must not be null
     * @param predicate  the predicate to use for validation, must not be null
     * @throws NullPointerException if queue or predicate is null
     * @throws IllegalArgumentException if the Queue contains invalid elements
     */
    protected PredicatedQueue(final Queue<E> queue, final Predicate<? super E> predicate) {
        super(queue, predicate);
    }

    /**
     * Gets the queue being decorated.
     *
     * @return the decorated queue
     */
    @Override
    protected Queue<E> decorated() {
        return (Queue<E>) super.decorated();
    }

    //-----------------------------------------------------------------------

    /**
     * Override to validate the object being added to ensure it matches
     * the predicate.
     *
     * @param object  the object being added
     * @return the result of adding to the underlying queue
     * @throws IllegalArgumentException if the add is invalid
     */
    @Override
    public boolean offer(final E object) {
        validate(object);
        return decorated().offer(object);
    }

    @Override
    public E poll() {
        return decorated().poll();
    }

    @Override
    public E peek() {
        return decorated().peek();
    }

    @Override
    public E element() {
        return decorated().element();
    }

    @Override
    public E remove() {
        return decorated().remove();
    }

}
