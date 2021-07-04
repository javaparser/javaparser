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

import java.io.Serializable;
import java.util.Collection;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.apache.commons.collections4.MapIterator;
import org.apache.commons.collections4.MultiSet;
import org.apache.commons.collections4.MultiValuedMap;

/**
 * Decorates another <code>MultiValuedMap</code> to provide additional behaviour.
 * <p>
 * Each method call made on this <code>MultiValuedMap</code> is forwarded to the
 * decorated <code>MultiValuedMap</code>. This class is used as a framework to build
 * to extensions such as synchronized and unmodifiable behaviour.
 *
 * @param <K> the type of key elements
 * @param <V> the type of value elements
 *
 * @since 4.1
 */
public abstract class AbstractMultiValuedMapDecorator<K, V>
        implements MultiValuedMap<K, V>, Serializable {

    /** Serialization version */
    private static final long serialVersionUID = 20150612L;

    /** MultiValuedMap to decorate */
    private final MultiValuedMap<K, V> map;

    /**
     * Constructor that wraps (not copies).
     *
     * @param map  the map to decorate, must not be null
     * @throws NullPointerException if the map is null
     */
    protected AbstractMultiValuedMapDecorator(final MultiValuedMap<K, V> map) {
        if (map == null) {
            throw new NullPointerException("MultiValuedMap must not be null.");
        }
        this.map = map;
    }

    // -----------------------------------------------------------------------
    /**
     * The decorated multi-valued map.
     *
     * @return the map to decorate
     */
    protected MultiValuedMap<K, V> decorated() {
        return map;
    }

    // -----------------------------------------------------------------------
    @Override
    public int size() {
        return decorated().size();
    }

    @Override
    public boolean isEmpty() {
        return decorated().isEmpty();
    }

    @Override
    public boolean containsKey(final Object key) {
        return decorated().containsKey(key);
    }

    @Override
    public boolean containsValue(final Object value) {
        return decorated().containsValue(value);
    }

    @Override
    public boolean containsMapping(final Object key, final Object value) {
        return decorated().containsMapping(key, value);
    }

    @Override
    public Collection<V> get(final K key) {
        return decorated().get(key);
    }

    @Override
    public Collection<V> remove(final Object key) {
        return decorated().remove(key);
    }

    @Override
    public boolean removeMapping(final Object key, final Object item) {
        return decorated().removeMapping(key, item);
    }

    @Override
    public void clear() {
        decorated().clear();
    }

    @Override
    public boolean put(final K key, final V value) {
        return decorated().put(key, value);
    }

    @Override
    public Set<K> keySet() {
        return decorated().keySet();
    }

    @Override
    public Collection<Entry<K, V>> entries() {
        return decorated().entries();
    }

    @Override
    public MultiSet<K> keys() {
        return decorated().keys();
    }

    @Override
    public Collection<V> values() {
        return decorated().values();
    }

    @Override
    public Map<K, Collection<V>> asMap() {
        return decorated().asMap();
    }

    @Override
    public boolean putAll(final K key, final Iterable<? extends V> values) {
        return decorated().putAll(key, values);
    }

    @Override
    public boolean putAll(final Map<? extends K, ? extends V> map) {
        return decorated().putAll(map);
    }

    @Override
    public boolean putAll(final MultiValuedMap<? extends K, ? extends V> map) {
        return decorated().putAll(map);
    }

    @Override
    public MapIterator<K, V> mapIterator() {
        return decorated().mapIterator();
    }

    @Override
    public boolean equals(final Object object) {
        if (object == this) {
            return true;
        }
        return decorated().equals(object);
    }

    @Override
    public int hashCode() {
        return decorated().hashCode();
    }

    @Override
    public String toString() {
        return decorated().toString();
    }

}
