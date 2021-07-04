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

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.util.Collection;
import java.util.Iterator;
import java.util.Queue;

import org.apache.commons.collections4.Unmodifiable;
import org.apache.commons.collections4.iterators.UnmodifiableIterator;

/**
 * Decorates another {@link Queue} to ensure it can't be altered.
 * <p>
 * Attempts to modify it will result in an UnsupportedOperationException.
 *
 * @param <E> the type of elements held in this queue
 * @since 4.0
 */
public final class UnmodifiableQueue<E>
        extends AbstractQueueDecorator<E>
        implements Unmodifiable {

    /** Serialization version */
    private static final long serialVersionUID = 1832948656215393357L;

    /**
     * Factory method to create an unmodifiable queue.
     * <p>
     * If the queue passed in is already unmodifiable, it is returned.
     *
     * @param <E> the type of the elements in the queue
     * @param queue  the queue to decorate, must not be null
     * @return an unmodifiable Queue
     * @throws NullPointerException if queue is null
     */
    public static <E> Queue<E> unmodifiableQueue(final Queue<? extends E> queue) {
        if (queue instanceof Unmodifiable) {
            @SuppressWarnings("unchecked") // safe to upcast
            final Queue<E> tmpQueue = (Queue<E>) queue;
            return tmpQueue;
        }
        return new UnmodifiableQueue<>(queue);
    }

    //-----------------------------------------------------------------------
    /**
     * Constructor that wraps (not copies).
     *
     * @param queue  the queue to decorate, must not be null
     * @throws NullPointerException if queue is null
     */
    @SuppressWarnings("unchecked") // safe to upcast
    private UnmodifiableQueue(final Queue<? extends E> queue) {
        super((Queue<E>) queue);
    }

    //-----------------------------------------------------------------------
    /**
     * Write the collection out using a custom routine.
     *
     * @param out  the output stream
     * @throws IOException if an I/O error occurs while writing to the output stream
     */
    private void writeObject(final ObjectOutputStream out) throws IOException {
        out.defaultWriteObject();
        out.writeObject(decorated());
    }

    /**
     * Read the collection in using a custom routine.
     *
     * @param in  the input stream
     * @throws IOException if an I/O error occurs while reading from the input stream
     * @throws ClassNotFoundException if the class of a serialized object can not be found
     */
    @SuppressWarnings("unchecked")
    private void readObject(final ObjectInputStream in) throws IOException, ClassNotFoundException {
        in.defaultReadObject();
        setCollection((Collection<E>) in.readObject());
    }

    //-----------------------------------------------------------------------
    @Override
    public Iterator<E> iterator() {
        return UnmodifiableIterator.unmodifiableIterator(decorated().iterator());
    }

    @Override
    public boolean add(final Object object) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean addAll(final Collection<? extends E> coll) {
        throw new UnsupportedOperationException();
    }

    @Override
    public void clear() {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean remove(final Object object) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean removeAll(final Collection<?> coll) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean retainAll(final Collection<?> coll) {
        throw new UnsupportedOperationException();
    }

    //-----------------------------------------------------------------------

    @Override
    public boolean offer(final E obj) {
        throw new UnsupportedOperationException();
    }

    @Override
    public E poll() {
        throw new UnsupportedOperationException();
    }

    @Override
    public E remove() {
        throw new UnsupportedOperationException();
    }

}
