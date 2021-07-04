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

import org.apache.commons.collections4.MapIterator;
import org.apache.commons.collections4.Unmodifiable;

/**
 * Decorates a map iterator such that it cannot be modified.
 * <p>
 * Attempts to modify it will result in an UnsupportedOperationException.
 *
 * @since 3.0
 */
public final class UnmodifiableMapIterator<K, V> implements MapIterator<K, V>, Unmodifiable {

    /** The iterator being decorated */
    private final MapIterator<? extends K, ? extends V> iterator;

    //-----------------------------------------------------------------------
    /**
     * Decorates the specified iterator such that it cannot be modified.
     *
     * @param <K>  the key type
     * @param <V>  the value type
     * @param iterator  the iterator to decorate
     * @return a new unmodifiable map iterator
     * @throws NullPointerException if the iterator is null
     */
    public static <K, V> MapIterator<K, V> unmodifiableMapIterator(
            final MapIterator<? extends K, ? extends V> iterator) {
        if (iterator == null) {
            throw new NullPointerException("MapIterator must not be null");
        }
        if (iterator instanceof Unmodifiable) {
            @SuppressWarnings("unchecked") // safe to upcast
            final MapIterator<K, V> tmpIterator = (MapIterator<K, V>) iterator;
            return tmpIterator;
        }
        return new UnmodifiableMapIterator<>(iterator);
    }

    //-----------------------------------------------------------------------
    /**
     * Constructor.
     *
     * @param iterator  the iterator to decorate
     */
    private UnmodifiableMapIterator(final MapIterator<? extends K, ? extends V> iterator) {
        super();
        this.iterator = iterator;
    }

    //-----------------------------------------------------------------------
    @Override
    public boolean hasNext() {
        return iterator.hasNext();
    }

    @Override
    public K next() {
        return iterator.next();
    }

    @Override
    public K getKey() {
        return iterator.getKey();
    }

    @Override
    public V getValue() {
        return iterator.getValue();
    }

    @Override
    public V setValue(final V value) {
        throw new UnsupportedOperationException("setValue() is not supported");
    }

    @Override
    public void remove() {
        throw new UnsupportedOperationException("remove() is not supported");
    }

}
