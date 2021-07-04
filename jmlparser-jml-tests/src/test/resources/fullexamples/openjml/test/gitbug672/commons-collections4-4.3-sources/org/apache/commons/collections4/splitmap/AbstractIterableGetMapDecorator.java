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
package org.apache.commons.collections4.splitmap;

import java.util.Collection;
import java.util.Map;
import java.util.Set;

import org.apache.commons.collections4.IterableGet;
import org.apache.commons.collections4.MapIterator;
import org.apache.commons.collections4.map.EntrySetToMapIteratorAdapter;

/**
 * {@link IterableGet} that uses a {@link Map}&lt;K, V&gt; for the
 * {@link org.apache.commons.collections4.Get Get}&lt;K, V&gt; implementation.
 *
 * @param <K> the type of the keys in this map
 * @param <V> the type of the values in this map
 * @since 4.0
 */
public class AbstractIterableGetMapDecorator<K, V> implements IterableGet<K, V> {

    /** The map to decorate */
    transient Map<K, V> map;

    /**
     * Create a new AbstractSplitMapDecorator.
     * @param map the map to decorate, must not be null
     * @throws NullPointerException if map is null
     */
    public AbstractIterableGetMapDecorator(final Map<K, V> map) {
        if (map == null) {
            throw new NullPointerException("Map must not be null.");
        }
        this.map = map;
    }

    /**
     * Constructor only used in deserialization, do not use otherwise.
     */
    protected AbstractIterableGetMapDecorator() {
        super();
    }

    /**
     * Gets the map being decorated.
     *
     * @return the decorated map
     */
    protected Map<K, V> decorated() {
        return map;
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
    public Set<Map.Entry<K, V>> entrySet() {
        return decorated().entrySet();
    }

    @Override
    public V get(final Object key) {
        return decorated().get(key);
    }

    @Override
    public V remove(final Object key) {
        return decorated().remove(key);
    }

    @Override
    public boolean isEmpty() {
        return decorated().isEmpty();
    }

    @Override
    public Set<K> keySet() {
        return decorated().keySet();
    }

    @Override
    public int size() {
        return decorated().size();
    }

    @Override
    public Collection<V> values() {
        return decorated().values();
    }

    /**
     * Get a MapIterator over this Get.
     * @return MapIterator&lt;K, V&gt;
     */
    @Override
    public MapIterator<K, V> mapIterator() {
        return new EntrySetToMapIteratorAdapter<>(entrySet());
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
