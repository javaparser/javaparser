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
package org.apache.commons.collections4.multimap;

import java.util.Collection;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.apache.commons.collections4.MapIterator;
import org.apache.commons.collections4.MultiSet;
import org.apache.commons.collections4.MultiValuedMap;
import org.apache.commons.collections4.Unmodifiable;
import org.apache.commons.collections4.collection.UnmodifiableCollection;
import org.apache.commons.collections4.iterators.UnmodifiableMapIterator;
import org.apache.commons.collections4.map.UnmodifiableMap;
import org.apache.commons.collections4.multiset.UnmodifiableMultiSet;
import org.apache.commons.collections4.set.UnmodifiableSet;

/**
 * Decorates another {@link MultiValuedMap} to ensure it can't be altered.
 * <p>
 * Attempts to modify it will result in an UnsupportedOperationException.
 *
 * @param <K> the type of key elements
 * @param <V> the type of value elements
 *
 * @since 4.1
 */
public final class UnmodifiableMultiValuedMap<K, V>
        extends AbstractMultiValuedMapDecorator<K, V> implements Unmodifiable {

    /** Serialization version */
    private static final long serialVersionUID = 20150612L;

    /**
     * Factory method to create an unmodifiable MultiValuedMap.
     * <p>
     * If the map passed in is already unmodifiable, it is returned.
     *
     * @param <K> the type of key elements
     * @param <V> the type of value elements
     * @param map  the map to decorate, may not be null
     * @return an unmodifiable MultiValuedMap
     * @throws NullPointerException if map is null
     */
    @SuppressWarnings("unchecked")
    public static <K, V> UnmodifiableMultiValuedMap<K, V> unmodifiableMultiValuedMap(
            final MultiValuedMap<? extends K, ? extends V> map) {
        if (map instanceof Unmodifiable) {
            return (UnmodifiableMultiValuedMap<K, V>) map;
        }
        return new UnmodifiableMultiValuedMap<>(map);
    }

    /**
     * Constructor that wraps (not copies).
     *
     * @param map  the MultiValuedMap to decorate, may not be null
     * @throws NullPointerException if the map is null
     */
    @SuppressWarnings("unchecked")
    private UnmodifiableMultiValuedMap(final MultiValuedMap<? extends K, ? extends V> map) {
        super((MultiValuedMap<K, V>) map);
    }

    @Override
    public Collection<V> remove(final Object key) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean removeMapping(final Object key, final Object item) {
        throw new UnsupportedOperationException();
    }

    @Override
    public void clear() {
        throw new UnsupportedOperationException();
    }

    @Override
    public Collection<V> get(final K key) {
        return UnmodifiableCollection.unmodifiableCollection(decorated().get(key));
    }

    @Override
    public boolean put(final K key, final V value) {
        throw new UnsupportedOperationException();
    }

    @Override
    public Set<K> keySet() {
        return UnmodifiableSet.unmodifiableSet(decorated().keySet());
    }

    @Override
    public Collection<Entry<K, V>> entries() {
        return UnmodifiableCollection.unmodifiableCollection(decorated().entries());
    }

    @Override
    public MultiSet<K> keys() {
        return UnmodifiableMultiSet.unmodifiableMultiSet(decorated().keys());
    }

    @Override
    public Collection<V> values() {
        return UnmodifiableCollection.unmodifiableCollection(decorated().values());
    }

    @Override
    public Map<K, Collection<V>> asMap() {
        return UnmodifiableMap.unmodifiableMap(decorated().asMap());
    }

    @Override
    public MapIterator<K, V> mapIterator() {
        return UnmodifiableMapIterator.unmodifiableMapIterator(decorated().mapIterator());
    }

    @Override
    public boolean putAll(final K key, final Iterable<? extends V> values) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean putAll(final Map<? extends K, ? extends V> map) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean putAll(final MultiValuedMap<? extends K, ? extends V> map) {
        throw new UnsupportedOperationException();
    }

}
