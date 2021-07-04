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

import java.util.Collection;
import java.util.Map;
import java.util.Set;

import org.apache.commons.collections4.collection.UnmodifiableCollection;
import org.apache.commons.collections4.iterators.UnmodifiableMapIterator;
import org.apache.commons.collections4.map.EntrySetToMapIteratorAdapter;
import org.apache.commons.collections4.map.UnmodifiableEntrySet;
import org.apache.commons.collections4.set.UnmodifiableSet;

/**
 * Utilities for working with "split maps:" objects that implement {@link Put}
 * and/or {@link Get} but not {@link Map}.
 *
 * @since 4.0
 *
 * @see Get
 * @see Put
 */
public class SplitMapUtils {

    /**
     * <code>SplitMapUtils</code> should not normally be instantiated.
     */
    private SplitMapUtils() {}

    //-----------------------------------------------------------------------

    private static class WrappedGet<K, V> implements IterableMap<K, V>, Unmodifiable {
        private final Get<K, V> get;

        private WrappedGet(final Get<K, V> get) {
            this.get = get;
        }

        @Override
        public void clear() {
            throw new UnsupportedOperationException();
        }

        @Override
        public boolean containsKey(final Object key) {
            return get.containsKey(key);
        }

        @Override
        public boolean containsValue(final Object value) {
            return get.containsValue(value);
        }

        @Override
        public Set<Map.Entry<K, V>> entrySet() {
            return UnmodifiableEntrySet.unmodifiableEntrySet(get.entrySet());
        }

        @Override
        public boolean equals(final Object arg0) {
            if (arg0 == this) {
                return true;
            }
            return arg0 instanceof WrappedGet && ((WrappedGet<?, ?>) arg0).get.equals(this.get);
        }

        @Override
        public V get(final Object key) {
            return get.get(key);
        }

        @Override
        public int hashCode() {
            return ("WrappedGet".hashCode() << 4) | get.hashCode();
        }

        @Override
        public boolean isEmpty() {
            return get.isEmpty();
        }

        @Override
        public Set<K> keySet() {
            return UnmodifiableSet.unmodifiableSet(get.keySet());
        }

        @Override
        public V put(final K key, final V value) {
            throw new UnsupportedOperationException();
        }

        @Override
        public void putAll(final Map<? extends K, ? extends V> t) {
            throw new UnsupportedOperationException();
        }

        @Override
        public V remove(final Object key) {
            return get.remove(key);
        }

        @Override
        public int size() {
            return get.size();
        }

        @Override
        public Collection<V> values() {
            return UnmodifiableCollection.unmodifiableCollection(get.values());
        }

        @Override
        public MapIterator<K, V> mapIterator() {
            MapIterator<K, V> it;
            if (get instanceof IterableGet) {
                it = ((IterableGet<K, V>) get).mapIterator();
            } else {
                it = new EntrySetToMapIteratorAdapter<>(get.entrySet());
            }
            return UnmodifiableMapIterator.unmodifiableMapIterator(it);
        }
    }

    private static class WrappedPut<K, V> implements Map<K, V>, Put<K, V> {
        private final Put<K, V> put;

        private WrappedPut(final Put<K, V> put) {
            this.put = put;
        }

        @Override
        public void clear() {
            put.clear();
        }

        @Override
        public boolean containsKey(final Object key) {
            throw new UnsupportedOperationException();
        }

        @Override
        public boolean containsValue(final Object value) {
            throw new UnsupportedOperationException();
        }

        @Override
        public Set<Map.Entry<K, V>> entrySet() {
            throw new UnsupportedOperationException();
        }

        @Override
        public boolean equals(final Object obj) {
            if (obj == this) {
                return true;
            }
            return obj instanceof WrappedPut && ((WrappedPut<?, ?>) obj).put.equals(this.put);
        }

        @Override
        public V get(final Object key) {
            throw new UnsupportedOperationException();
        }

        @Override
        public int hashCode() {
            return ("WrappedPut".hashCode() << 4) | put.hashCode();
        }

        @Override
        public boolean isEmpty() {
            throw new UnsupportedOperationException();
        }

        @Override
        public Set<K> keySet() {
            throw new UnsupportedOperationException();
        }

        @Override
        @SuppressWarnings("unchecked")
        public V put(final K key, final V value) {
            return (V) put.put(key, value);
        }

        @Override
        public void putAll(final Map<? extends K, ? extends V> t) {
            put.putAll(t);
        }

        @Override
        public V remove(final Object key) {
            throw new UnsupportedOperationException();
        }

        @Override
        public int size() {
            throw new UnsupportedOperationException();
        }

        @Override
        public Collection<V> values() {
            throw new UnsupportedOperationException();
        }
    }

    //-----------------------------------------------------------------------

    /**
     * Get the specified {@link Get} as an instance of {@link IterableMap}.
     * If <code>get</code> implements {@link IterableMap} directly, no conversion will take place.
     * If <code>get</code> implements {@link Map} but not {@link IterableMap} it will be decorated.
     * Otherwise an {@link Unmodifiable} {@link IterableMap} will be returned.
     * @param <K> the key type
     * @param <V> the value type
     * @param get to wrap, must not be null
     * @return {@link IterableMap}
     * @throws NullPointerException if the argument is null
     */
    @SuppressWarnings("unchecked")
    public static <K, V> IterableMap<K, V> readableMap(final Get<K, V> get) {
        if (get == null) {
            throw new NullPointerException("Get must not be null");
        }
        if (get instanceof Map) {
            return get instanceof IterableMap ?
                    ((IterableMap<K, V>) get) :
                    MapUtils.iterableMap((Map<K, V>) get);
        }
        return new WrappedGet<>(get);
    }

    /**
     * Get the specified {@link Put} as an instanceof {@link Map}.
     * If <code>put</code> implements {@link Map} directly, no conversion will take place.
     * Otherwise a <em>write-only</em> {@link Map} will be returned.  On such a {@link Map}
     * it is recommended that the result of #put(K, V) be discarded as it likely will not
     * match <code>V</code> at runtime.
     *
     * @param <K> the key type
     * @param <V> the element type
     * @param put to wrap, must not be null
     * @return {@link Map}
     * @throws NullPointerException if the argument is null
     */
    @SuppressWarnings("unchecked")
    public static <K, V> Map<K, V> writableMap(final Put<K, V> put) {
        if (put == null) {
            throw new NullPointerException("Put must not be null");
        }
        if (put instanceof Map) {
            return (Map<K, V>) put;
        }
        return new WrappedPut<>(put);
    }

}
