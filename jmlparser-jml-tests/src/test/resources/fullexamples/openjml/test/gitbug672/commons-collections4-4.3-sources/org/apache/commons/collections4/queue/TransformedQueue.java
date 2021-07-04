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

import org.apache.commons.collections4.Transformer;
import org.apache.commons.collections4.collection.TransformedCollection;

/**
 * Decorates another {@link Queue} to transform objects that are added.
 * <p>
 * The add/offer methods are affected by this class.
 * Thus objects must be removed or searched for using their transformed form.
 * For example, if the transformation converts Strings to Integers, you must
 * use the Integer form to remove objects.
 *
 * @param <E> the type of elements held in this queue
 * @since 4.0
 */
public class TransformedQueue<E> extends TransformedCollection<E> implements Queue<E> {

    /** Serialization version */
    private static final long serialVersionUID = -7901091318986132033L;

    /**
     * Factory method to create a transforming queue.
     * <p>
     * If there are any elements already in the queue being decorated, they
     * are NOT transformed.
     * Contrast this with {@link #transformedQueue(Queue, Transformer)}.
     *
     * @param <E> the type of the elements in the queue
     * @param queue  the queue to decorate, must not be null
     * @param transformer  the transformer to use for conversion, must not be null
     * @return a new transformed Queue
     * @throws NullPointerException if queue or transformer is null
     */
    public static <E> TransformedQueue<E> transformingQueue(final Queue<E> queue,
                                                            final Transformer<? super E, ? extends E> transformer) {
        return new TransformedQueue<>(queue, transformer);
    }

    /**
     * Factory method to create a transforming queue that will transform
     * existing contents of the specified queue.
     * <p>
     * If there are any elements already in the queue being decorated, they
     * will be transformed by this method.
     * Contrast this with {@link #transformingQueue(Queue, Transformer)}.
     *
     * @param <E> the type of the elements in the queue
     * @param queue  the queue to decorate, must not be null
     * @param transformer  the transformer to use for conversion, must not be null
     * @return a new transformed Queue
     * @throws NullPointerException if queue or transformer is null
     * @since 4.0
     */
    public static <E> TransformedQueue<E> transformedQueue(final Queue<E> queue,
                                                           final Transformer<? super E, ? extends E> transformer) {
        // throws IAE if queue or transformer is null
        final TransformedQueue<E> decorated = new TransformedQueue<>(queue, transformer);
        if (queue.size() > 0) {
            @SuppressWarnings("unchecked") // queue is type <E>
            final E[] values = (E[]) queue.toArray(); // NOPMD - false positive for generics
            queue.clear();
            for (final E value : values) {
                decorated.decorated().add(transformer.transform(value));
            }
        }
        return decorated;
    }

    //-----------------------------------------------------------------------
    /**
     * Constructor that wraps (not copies).
     * <p>
     * If there are any elements already in the queue being decorated, they
     * are NOT transformed.
     *
     * @param queue  the queue to decorate, must not be null
     * @param transformer  the transformer to use for conversion, must not be null
     * @throws NullPointerException if queue or transformer is null
     */
    protected TransformedQueue(final Queue<E> queue, final Transformer<? super E, ? extends E> transformer) {
        super(queue, transformer);
    }

    /**
     * Gets the decorated queue.
     *
     * @return the decorated queue
     */
    protected Queue<E> getQueue() {
        return (Queue<E>) decorated();
    }

    //-----------------------------------------------------------------------

    @Override
    public boolean offer(final E obj) {
        return getQueue().offer(transform(obj));
    }

    @Override
    public E poll() {
        return getQueue().poll();
    }

    @Override
    public E peek() {
        return getQueue().peek();
    }

    @Override
    public E element() {
        return getQueue().element();
    }

    @Override
    public E remove() {
        return getQueue().remove();
    }

}
