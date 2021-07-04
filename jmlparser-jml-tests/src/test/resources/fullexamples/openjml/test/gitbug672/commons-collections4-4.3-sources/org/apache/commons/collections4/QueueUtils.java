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
package org.apache.commons.collections4;

import java.util.LinkedList;
import java.util.Queue;

import org.apache.commons.collections4.queue.PredicatedQueue;
import org.apache.commons.collections4.queue.SynchronizedQueue;
import org.apache.commons.collections4.queue.TransformedQueue;
import org.apache.commons.collections4.queue.UnmodifiableQueue;

/**
 * Provides utility methods and decorators for {@link Queue} instances.
 *
 * @since 4.0
 */
public class QueueUtils {

    /**
     * An empty unmodifiable queue.
     */
    @SuppressWarnings("rawtypes") // OK, empty queue is compatible with any type
    public static final Queue EMPTY_QUEUE = UnmodifiableQueue.unmodifiableQueue(new LinkedList<>());

    /**
     * <code>QueueUtils</code> should not normally be instantiated.
     */
    private QueueUtils() {}

    //-----------------------------------------------------------------------

    /**
     * Returns a synchronized (thread-safe) queue backed by the given queue.
     * In order to guarantee serial access, it is critical that all access to the
     * backing queue is accomplished through the returned queue.
     * <p>
     * It is imperative that the user manually synchronize on the returned queue
     * when iterating over it:
     *
     * <pre>
     * Queue queue = QueueUtils.synchronizedQueue(new CircularFifoQueue());
     * ...
     * synchronized(queue) {
     *     Iterator i = queue.iterator(); // Must be in synchronized block
     *     while (i.hasNext())
     *         foo(i.next());
     *     }
     * }
     * </pre>
     *
     * Failure to follow this advice may result in non-deterministic behavior.
     *
     * @param <E> the element type
     * @param queue the queue to synchronize, must not be null
     * @return a synchronized queue backed by that queue
     * @throws NullPointerException if the queue is null
     * @since 4.2
     */
    public static <E> Queue<E> synchronizedQueue(final Queue<E> queue) {
        return SynchronizedQueue.synchronizedQueue(queue);
    }

    /**
     * Returns an unmodifiable queue backed by the given queue.
     *
     * @param <E> the type of the elements in the queue
     * @param queue  the queue to make unmodifiable, must not be null
     * @return an unmodifiable queue backed by that queue
     * @throws NullPointerException if the queue is null
     */
    public static <E> Queue<E> unmodifiableQueue(final Queue<? extends E> queue) {
        return UnmodifiableQueue.unmodifiableQueue(queue);
    }

    /**
     * Returns a predicated (validating) queue backed by the given queue.
     * <p>
     * Only objects that pass the test in the given predicate can be added to the queue.
     * Trying to add an invalid object results in an IllegalArgumentException.
     * It is important not to use the original queue after invoking this method,
     * as it is a backdoor for adding invalid objects.
     *
     * @param <E> the type of the elements in the queue
     * @param queue  the queue to predicate, must not be null
     * @param predicate  the predicate used to evaluate new elements, must not be null
     * @return a predicated queue
     * @throws NullPointerException if the queue or predicate is null
     */
    public static <E> Queue<E> predicatedQueue(final Queue<E> queue, final Predicate<? super E> predicate) {
        return PredicatedQueue.predicatedQueue(queue, predicate);
    }

    /**
     * Returns a transformed queue backed by the given queue.
     * <p>
     * Each object is passed through the transformer as it is added to the
     * Queue. It is important not to use the original queue after invoking this
     * method, as it is a backdoor for adding untransformed objects.
     * <p>
     * Existing entries in the specified queue will not be transformed.
     * If you want that behaviour, see {@link TransformedQueue#transformedQueue}.
     *
     * @param <E> the type of the elements in the queue
     * @param queue  the queue to predicate, must not be null
     * @param transformer  the transformer for the queue, must not be null
     * @return a transformed queue backed by the given queue
     * @throws NullPointerException if the queue or transformer is null
     */
    public static <E> Queue<E> transformingQueue(final Queue<E> queue,
                                                 final Transformer<? super E, ? extends E> transformer) {
        return TransformedQueue.transformingQueue(queue, transformer);
    }

    /**
     * Get an empty <code>Queue</code>.
     *
     * @param <E> the type of the elements in the queue
     * @return an empty {@link Queue}
     */
    @SuppressWarnings("unchecked") // OK, empty queue is compatible with any type
    public static <E> Queue<E> emptyQueue() {
        return EMPTY_QUEUE;
    }
}
