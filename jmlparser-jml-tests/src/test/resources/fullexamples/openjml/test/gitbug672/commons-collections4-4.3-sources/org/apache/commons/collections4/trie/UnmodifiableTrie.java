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
package org.apache.commons.collections4.trie;

import java.io.Serializable;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;

import org.apache.commons.collections4.OrderedMapIterator;
import org.apache.commons.collections4.Trie;
import org.apache.commons.collections4.Unmodifiable;
import org.apache.commons.collections4.iterators.UnmodifiableOrderedMapIterator;

/**
 * An unmodifiable {@link Trie}.
 *
 * @param <K> the type of the keys in this map
 * @param <V> the type of the values in this map
 * @since 4.0
 */
public class UnmodifiableTrie<K, V> implements Trie<K, V>, Serializable, Unmodifiable {

    /** Serialization version */
    private static final long serialVersionUID = -7156426030315945159L;

    private final Trie<K, V> delegate;

    /**
     * Factory method to create a unmodifiable trie.
     *
     * @param <K>  the key type
     * @param <V>  the value type
     * @param trie  the trie to decorate, must not be null
     * @return a new unmodifiable trie
     * @throws NullPointerException if trie is null
     */
    public static <K, V> Trie<K, V> unmodifiableTrie(final Trie<K, ? extends V> trie) {
        if (trie instanceof Unmodifiable) {
            @SuppressWarnings("unchecked") // safe to upcast
            final Trie<K, V> tmpTrie = (Trie<K, V>) trie;
            return tmpTrie;
        }
        return new UnmodifiableTrie<>(trie);
    }

    //-----------------------------------------------------------------------
    /**
     * Constructor that wraps (not copies).
     *
     * @param trie  the trie to decorate, must not be null
     * @throws NullPointerException if trie is null
     */
    public UnmodifiableTrie(final Trie<K, ? extends V> trie) {
        if (trie == null) {
            throw new NullPointerException("Trie must not be null");
        }
        @SuppressWarnings("unchecked") // safe to upcast
        final Trie<K, V> tmpTrie = (Trie<K, V>) trie;
        this.delegate = tmpTrie;
    }

    //-----------------------------------------------------------------------

    @Override
    public Set<Entry<K, V>> entrySet() {
        return Collections.unmodifiableSet(delegate.entrySet());
    }

    @Override
    public Set<K> keySet() {
        return Collections.unmodifiableSet(delegate.keySet());
    }

    @Override
    public Collection<V> values() {
        return Collections.unmodifiableCollection(delegate.values());
    }

    @Override
    public void clear() {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean containsKey(final Object key) {
        return delegate.containsKey(key);
    }

    @Override
    public boolean containsValue(final Object value) {
        return delegate.containsValue(value);
    }

    @Override
    public V get(final Object key) {
        return delegate.get(key);
    }

    @Override
    public boolean isEmpty() {
        return delegate.isEmpty();
    }

    @Override
    public V put(final K key, final V value) {
        throw new UnsupportedOperationException();
    }

    @Override
    public void putAll(final Map<? extends K, ? extends V> m) {
        throw new UnsupportedOperationException();
    }

    @Override
    public V remove(final Object key) {
        throw new UnsupportedOperationException();
    }

    @Override
    public int size() {
        return delegate.size();
    }

    @Override
    public K firstKey() {
        return delegate.firstKey();
    }

    @Override
    public SortedMap<K, V> headMap(final K toKey) {
        return Collections.unmodifiableSortedMap(delegate.headMap(toKey));
    }

    @Override
    public K lastKey() {
        return delegate.lastKey();
    }

    @Override
    public SortedMap<K, V> subMap(final K fromKey, final K toKey) {
        return Collections.unmodifiableSortedMap(delegate.subMap(fromKey, toKey));
    }

    @Override
    public SortedMap<K, V> tailMap(final K fromKey) {
        return Collections.unmodifiableSortedMap(delegate.tailMap(fromKey));
    }

    @Override
    public SortedMap<K, V> prefixMap(final K key) {
        return Collections.unmodifiableSortedMap(delegate.prefixMap(key));
    }

    @Override
    public Comparator<? super K> comparator() {
        return delegate.comparator();
    }

    //-----------------------------------------------------------------------
    @Override
    public OrderedMapIterator<K, V> mapIterator() {
        final OrderedMapIterator<K, V> it = delegate.mapIterator();
        return UnmodifiableOrderedMapIterator.unmodifiableOrderedMapIterator(it);
    }

    @Override
    public K nextKey(final K key) {
        return delegate.nextKey(key);
    }

    @Override
    public K previousKey(final K key) {
        return delegate.previousKey(key);
    }

    //-----------------------------------------------------------------------
    @Override
    public int hashCode() {
        return delegate.hashCode();
    }

    @Override
    public boolean equals(final Object obj) {
        return delegate.equals(obj);
    }

    @Override
    public String toString() {
        return delegate.toString();
    }

}
