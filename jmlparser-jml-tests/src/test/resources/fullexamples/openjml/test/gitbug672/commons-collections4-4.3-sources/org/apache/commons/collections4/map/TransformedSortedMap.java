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
import java.util.Map;
import java.util.SortedMap;

import org.apache.commons.collections4.Transformer;

/**
 * Decorates another <code>SortedMap </code> to transform objects that are added.
 * <p>
 * The Map put methods and Map.Entry setValue method are affected by this class.
 * Thus objects must be removed or searched for using their transformed form.
 * For example, if the transformation converts Strings to Integers, you must
 * use the Integer form to remove objects.
 * <p>
 * <strong>Note that TransformedSortedMap is not synchronized and is not thread-safe.</strong>
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
public class TransformedSortedMap<K, V>
        extends TransformedMap<K, V>
        implements SortedMap<K, V> {

    /** Serialization version */
    private static final long serialVersionUID = -8751771676410385778L;

    /**
     * Factory method to create a transforming sorted map.
     * <p>
     * If there are any elements already in the map being decorated, they are NOT transformed.
     * Contrast this with {@link #transformedSortedMap(SortedMap, Transformer, Transformer)}.
     *
     * @param <K>  the key type
     * @param <V>  the value type
     * @param map  the map to decorate, must not be null
     * @param keyTransformer  the predicate to validate the keys, null means no transformation
     * @param valueTransformer  the predicate to validate to values, null means no transformation
     * @return a new transformed sorted map
     * @throws NullPointerException if the map is null
     * @since 4.0
     */
    public static <K, V> TransformedSortedMap<K, V> transformingSortedMap(final SortedMap<K, V> map,
            final Transformer<? super K, ? extends K> keyTransformer,
            final Transformer<? super V, ? extends V> valueTransformer) {
        return new TransformedSortedMap<>(map, keyTransformer, valueTransformer);
    }

    /**
     * Factory method to create a transforming sorted map that will transform
     * existing contents of the specified map.
     * <p>
     * If there are any elements already in the map being decorated, they
     * will be transformed by this method.
     * Contrast this with {@link #transformingSortedMap(SortedMap, Transformer, Transformer)}.
     *
     * @param <K>  the key type
     * @param <V>  the value type
     * @param map  the map to decorate, must not be null
     * @param keyTransformer  the transformer to use for key conversion, null means no transformation
     * @param valueTransformer  the transformer to use for value conversion, null means no transformation
     * @return a new transformed sorted map
     * @throws NullPointerException if map is null
     * @since 4.0
     */
    public static <K, V> TransformedSortedMap<K, V> transformedSortedMap(final SortedMap<K, V> map,
            final Transformer<? super K, ? extends K> keyTransformer,
            final Transformer<? super V, ? extends V> valueTransformer) {

        final TransformedSortedMap<K, V> decorated =
                new TransformedSortedMap<>(map, keyTransformer, valueTransformer);
        if (map.size() > 0) {
            final Map<K, V> transformed = decorated.transformMap(map);
            decorated.clear();
            decorated.decorated().putAll(transformed);  // avoids double transformation
        }
        return decorated;
    }

    //-----------------------------------------------------------------------
    /**
     * Constructor that wraps (not copies).
     * <p>
     * If there are any elements already in the collection being decorated, they
     * are NOT transformed.</p>
     *
     * @param map  the map to decorate, must not be null
     * @param keyTransformer  the predicate to validate the keys, null means no transformation
     * @param valueTransformer  the predicate to validate to values, null means no transformation
     * @throws NullPointerException if the map is null
     */
    protected TransformedSortedMap(final SortedMap<K, V> map,
            final Transformer<? super K, ? extends K> keyTransformer,
            final Transformer<? super V, ? extends V> valueTransformer) {
        super(map, keyTransformer, valueTransformer);
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
        return new TransformedSortedMap<>(map, keyTransformer, valueTransformer);
    }

    @Override
    public SortedMap<K, V> headMap(final K toKey) {
        final SortedMap<K, V> map = getSortedMap().headMap(toKey);
        return new TransformedSortedMap<>(map, keyTransformer, valueTransformer);
    }

    @Override
    public SortedMap<K, V> tailMap(final K fromKey) {
        final SortedMap<K, V> map = getSortedMap().tailMap(fromKey);
        return new TransformedSortedMap<>(map, keyTransformer, valueTransformer);
    }

}
