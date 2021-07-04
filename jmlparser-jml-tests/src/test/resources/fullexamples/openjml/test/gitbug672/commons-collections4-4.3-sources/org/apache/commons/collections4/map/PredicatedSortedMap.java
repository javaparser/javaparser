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
package org.apache.commons.collections4.map;

import java.util.Comparator;
import java.util.SortedMap;

import org.apache.commons.collections4.Predicate;

/**
 * Decorates another <code>SortedMap</code> to validate that additions
 * match a specified predicate.
 * <p>
 * This map exists to provide validation for the decorated map.
 * It is normally created to decorate an empty map.
 * If an object cannot be added to the map, an IllegalArgumentException is thrown.
 * <p>
 * One usage would be to ensure that no null keys are added to the map.
 * <pre>
 *   SortedMap map =
 *     PredicatedSortedMap.predicatedSortedMap(new TreeMap(),
 *                                             NotNullPredicate.notNullPredicate(),
 *                                             null);
 * </pre>
 * <p>
 * <strong>Note that PredicatedSortedMap is not synchronized and is not thread-safe.</strong>
 * If you wish to use this map from multiple threads concurrently, you must use
 * appropriate synchronization. The simplest approach is to wrap this map
 * using {@link java.util.Collections#synchronizedSortedMap}. This class may throw
 * exceptions when accessed by concurrent threads without synchronization.
 * <p>
 * This class is Serializable from Commons Collections 3.1.
 *
 * @param <K> the type of the keys in this map
 * @param <V> the type of the values in this map
 * @since 3.0
 */
public class PredicatedSortedMap<K, V> extends PredicatedMap<K, V> implements SortedMap<K, V> {

    /** Serialization version */
    private static final long serialVersionUID = 3359846175935304332L;

    /**
     * Factory method to create a predicated (validating) sorted map.
     * <p>
     * If there are any elements already in the list being decorated, they
     * are validated.
     *
     * @param <K>  the key type
     * @param <V>  the value type
     * @param map  the map to decorate, must not be null
     * @param keyPredicate  the predicate to validate the keys, null means no check
     * @param valuePredicate  the predicate to validate to values, null means no check
     * @return a new predicated sorted map
     * @throws NullPointerException if the map is null
     * @since 4.0
     */
    public static <K, V> PredicatedSortedMap<K, V> predicatedSortedMap(final SortedMap<K, V> map,
            final Predicate<? super K> keyPredicate, final Predicate<? super V> valuePredicate) {
        return new PredicatedSortedMap<>(map, keyPredicate, valuePredicate);
    }

    //-----------------------------------------------------------------------
    /**
     * Constructor that wraps (not copies).
     *
     * @param map  the map to decorate, must not be null
     * @param keyPredicate  the predicate to validate the keys, null means no check
     * @param valuePredicate  the predicate to validate to values, null means no check
     * @throws NullPointerException if the map is null
     */
    protected PredicatedSortedMap(final SortedMap<K, V> map, final Predicate<? super K> keyPredicate,
            final Predicate<? super V> valuePredicate) {
        super(map, keyPredicate, valuePredicate);
    }

    //-----------------------------------------------------------------------
    /**
     * Gets the map being decorated.
     *
     * @return the decorated map
     */
    protected SortedMap<K, V> getSortedMap() {
        return (SortedMap<K, V>) map;
    }

    //-----------------------------------------------------------------------
    @Override
    public K firstKey() {
        return getSortedMap().firstKey();
    }

    @Override
    public K lastKey() {
        return getSortedMap().lastKey();
    }

    @Override
    public Comparator<? super K> comparator() {
        return getSortedMap().comparator();
    }

    @Override
    public SortedMap<K, V> subMap(final K fromKey, final K toKey) {
        final SortedMap<K, V> map = getSortedMap().subMap(fromKey, toKey);
        return new PredicatedSortedMap<>(map, keyPredicate, valuePredicate);
    }

    @Override
    public SortedMap<K, V> headMap(final K toKey) {
        final SortedMap<K, V> map = getSortedMap().headMap(toKey);
        return new PredicatedSortedMap<>(map, keyPredicate, valuePredicate);
    }

    @Override
    public SortedMap<K, V> tailMap(final K fromKey) {
        final SortedMap<K, V> map = getSortedMap().tailMap(fromKey);
        return new PredicatedSortedMap<>(map, keyPredicate, valuePredicate);
    }

}
