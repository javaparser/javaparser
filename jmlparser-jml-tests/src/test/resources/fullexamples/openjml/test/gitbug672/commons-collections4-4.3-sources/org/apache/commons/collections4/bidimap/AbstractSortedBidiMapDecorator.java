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
package org.apache.commons.collections4.bidimap;

import java.util.Comparator;
import java.util.SortedMap;

import org.apache.commons.collections4.SortedBidiMap;

/**
 * Provides a base decorator that enables additional functionality to be added
 * to a SortedBidiMap via decoration.
 * <p>
 * Methods are forwarded directly to the decorated map.
 * <p>
 * This implementation does not perform any special processing with the map views.
 * Instead it simply returns the inverse from the wrapped map. This may be
 * undesirable, for example if you are trying to write a validating implementation
 * it would provide a loophole around the validation.
 * But, you might want that loophole, so this class is kept simple.
 *
 * @param <K> the type of the keys in this map
 * @param <V> the type of the values in this map
 * @since 3.0
 */
public abstract class AbstractSortedBidiMapDecorator<K, V>
        extends AbstractOrderedBidiMapDecorator<K, V> implements SortedBidiMap<K, V> {

    /**
     * Constructor that wraps (not copies).
     *
     * @param map  the map to decorate, must not be null
     * @throws NullPointerException if the collection is null
     */
    public AbstractSortedBidiMapDecorator(final SortedBidiMap<K, V> map) {
        super(map);
    }

    /**
     * Gets the map being decorated.
     *
     * @return the decorated map
     */
    @Override
    protected SortedBidiMap<K, V> decorated() {
        return (SortedBidiMap<K, V>) super.decorated();
    }

    //-----------------------------------------------------------------------
    @Override
    public SortedBidiMap<V, K> inverseBidiMap() {
        return decorated().inverseBidiMap();
    }

    @Override
    public Comparator<? super K> comparator() {
        return decorated().comparator();
    }

    @Override
    public Comparator<? super V> valueComparator() {
        return decorated().valueComparator();
    }

    @Override
    public SortedMap<K, V> subMap(final K fromKey, final K toKey) {
        return decorated().subMap(fromKey, toKey);
    }

    @Override
    public SortedMap<K, V> headMap(final K toKey) {
        return decorated().headMap(toKey);
    }

    @Override
    public SortedMap<K, V> tailMap(final K fromKey) {
        return decorated().tailMap(fromKey);
    }

}
