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
package org.apache.commons.collections4.multiset;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.util.Collection;
import java.util.Iterator;
import java.util.Set;

import org.apache.commons.collections4.MultiSet;
import org.apache.commons.collections4.Unmodifiable;
import org.apache.commons.collections4.iterators.UnmodifiableIterator;
import org.apache.commons.collections4.set.UnmodifiableSet;

/**
 * Decorates another {@link MultiSet} to ensure it can't be altered.
 * <p>
 * Attempts to modify it will result in an UnsupportedOperationException.
 *
 * @param <E> the type held in the multiset
 * @since 4.1
 */
public final class UnmodifiableMultiSet<E>
        extends AbstractMultiSetDecorator<E> implements Unmodifiable {

    /** Serialization version */
    private static final long serialVersionUID = 20150611L;

    /**
     * Factory method to create an unmodifiable multiset.
     * <p>
     * If the multiset passed in is already unmodifiable, it is returned.
     *
     * @param <E>  the type of the elements in the multiset
     * @param multiset  the multiset to decorate, may not be null
     * @return an unmodifiable MultiSet
     * @throws NullPointerException if multiset is null
     */
    public static <E> MultiSet<E> unmodifiableMultiSet(final MultiSet<? extends E> multiset) {
        if (multiset instanceof Unmodifiable) {
            @SuppressWarnings("unchecked") // safe to upcast
            final MultiSet<E> tmpMultiSet = (MultiSet<E>) multiset;
            return tmpMultiSet;
        }
        return new UnmodifiableMultiSet<>(multiset);
    }

    //-----------------------------------------------------------------------
    /**
     * Constructor that wraps (not copies).
     *
     * @param multiset  the multiset to decorate, may not be null
     * @throws NullPointerException if multiset is null
     */
    @SuppressWarnings("unchecked") // safe to upcast
    private UnmodifiableMultiSet(final MultiSet<? extends E> multiset) {
        super((MultiSet<E>) multiset);
    }

    //-----------------------------------------------------------------------
    /**
     * Write the collection out using a custom routine.
     *
     * @param out  the output stream
     * @throws IOException if an error occurs while writing to the stream
     */
    private void writeObject(final ObjectOutputStream out) throws IOException {
        out.defaultWriteObject();
        out.writeObject(decorated());
    }

    /**
     * Read the collection in using a custom routine.
     *
     * @param in  the input stream
     * @throws IOException if an error occurs while reading from the stream
     * @throws ClassNotFoundException if an object read from the stream can not be loaded
     * @throws ClassCastException if deserialised object has wrong type
     */
    @SuppressWarnings("unchecked") // will throw CCE, see Javadoc
    private void readObject(final ObjectInputStream in) throws IOException, ClassNotFoundException {
        in.defaultReadObject();
        setCollection((Collection<E>) in.readObject());
    }

    //-----------------------------------------------------------------------
    @Override
    public Iterator<E> iterator() {
        return UnmodifiableIterator.<E> unmodifiableIterator(decorated().iterator());
    }

    @Override
    public boolean add(final E object) {
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
    public int setCount(final E object, final int count) {
        throw new UnsupportedOperationException();
    }

    @Override
    public int add(final E object, final int count) {
        throw new UnsupportedOperationException();
    }

    @Override
    public int remove(final Object object, final int count) {
        throw new UnsupportedOperationException();
    }

    @Override
    public Set<E> uniqueSet() {
        final Set<E> set = decorated().uniqueSet();
        return UnmodifiableSet.unmodifiableSet(set);
    }

    @Override
    public Set<MultiSet.Entry<E>> entrySet() {
        final Set<MultiSet.Entry<E>> set = decorated().entrySet();
        return UnmodifiableSet.unmodifiableSet(set);
    }

}
