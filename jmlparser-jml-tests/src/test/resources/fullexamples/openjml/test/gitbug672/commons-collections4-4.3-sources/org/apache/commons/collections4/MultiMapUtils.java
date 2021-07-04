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

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.apache.commons.collections4.bag.HashBag;
import org.apache.commons.collections4.multimap.ArrayListValuedHashMap;
import org.apache.commons.collections4.multimap.HashSetValuedHashMap;
import org.apache.commons.collections4.multimap.TransformedMultiValuedMap;
import org.apache.commons.collections4.multimap.UnmodifiableMultiValuedMap;

/**
 * Provides utility methods and decorators for {@link MultiValuedMap} instances.
 * <p>
 * It contains various type safe and null safe methods. Additionally, it provides
 * the following decorators:
 * <ul>
 *   <li>{@link #unmodifiableMultiValuedMap(MultiValuedMap)}</li>
 *   <li>{@link #transformedMultiValuedMap(MultiValuedMap, Transformer, Transformer)}</li>
 * </ul>
 *
 * @since 4.1
 */
public class MultiMapUtils {

    /**
     * <code>MultiMapUtils</code> should not normally be instantiated.
     */
    private MultiMapUtils() {}

    /**
     * An empty {@link UnmodifiableMultiValuedMap}.
     */
    @SuppressWarnings({ "rawtypes", "unchecked" })
    public static final MultiValuedMap EMPTY_MULTI_VALUED_MAP =
            UnmodifiableMultiValuedMap.unmodifiableMultiValuedMap(new ArrayListValuedHashMap(0, 0));

    /**
     * Returns immutable EMPTY_MULTI_VALUED_MAP with generic type safety.
     *
     * @param <K> the type of key in the map
     * @param <V> the type of value in the map
     * @return immutable and empty <code>MultiValuedMap</code>
     */
    @SuppressWarnings("unchecked")
    public static <K, V> MultiValuedMap<K, V> emptyMultiValuedMap() {
        return EMPTY_MULTI_VALUED_MAP;
    }

    // Null safe methods

    /**
     * Returns an immutable empty <code>MultiValuedMap</code> if the argument is
     * <code>null</code>, or the argument itself otherwise.
     *
     * @param <K> the type of key in the map
     * @param <V> the type of value in the map
     * @param map  the map, may be null
     * @return an empty {@link MultiValuedMap} if the argument is null
     */
    @SuppressWarnings("unchecked")
    public static <K, V> MultiValuedMap<K, V> emptyIfNull(final MultiValuedMap<K, V> map) {
        return map == null ? EMPTY_MULTI_VALUED_MAP : map;
    }

    /**
     * Null-safe check if the specified <code>MultiValuedMap</code> is empty.
     * <p>
     * If the provided map is null, returns true.
     *
     * @param map  the map to check, may be null
     * @return true if the map is empty or null
     */
    public static boolean isEmpty(final MultiValuedMap<?, ?> map) {
        return map == null || map.isEmpty();
    }

    // Null safe getters
    // -------------------------------------------------------------------------

    /**
     * Gets a Collection from <code>MultiValuedMap</code> in a null-safe manner.
     *
     * @param <K> the key type
     * @param <V> the value type
     * @param map  the {@link MultiValuedMap} to use
     * @param key  the key to look up
     * @return the Collection in the {@link MultiValuedMap}, or null if input map is null
     */
    public static <K, V> Collection<V> getCollection(final MultiValuedMap<K, V> map, final K key) {
        if (map != null) {
            return map.get(key);
        }
        return null;
    }

    // TODO: review the getValuesAsXXX methods - depending on the actual MultiValuedMap type, changes
    // to the returned collection might update the backing map. This should be clarified and/or prevented.

    /**
     * Gets a List from <code>MultiValuedMap</code> in a null-safe manner.
     *
     * @param <K> the key type
     * @param <V> the value type
     * @param map  the {@link MultiValuedMap} to use
     * @param key  the key to look up
     * @return the Collection in the {@link MultiValuedMap} as List, or null if input map is null
     */
    public static <K, V> List<V> getValuesAsList(final MultiValuedMap<K, V> map, final K key) {
        if (map != null) {
            final Collection<V> col = map.get(key);
            if (col instanceof List) {
                return (List<V>) col;
            }
            return new ArrayList<>(col);
        }
        return null;
    }

    /**
     * Gets a Set from <code>MultiValuedMap</code> in a null-safe manner.
     *
     * @param <K> the key type
     * @param <V> the value type
     * @param map  the {@link MultiValuedMap} to use
     * @param key  the key to look up
     * @return the Collection in the {@link MultiValuedMap} as Set, or null if input map is null
     */
    public static <K, V> Set<V> getValuesAsSet(final MultiValuedMap<K, V> map, final K key) {
        if (map != null) {
            final Collection<V> col = map.get(key);
            if (col instanceof Set) {
                return (Set<V>) col;
            }
            return new HashSet<>(col);
        }
        return null;
    }

    /**
     * Gets a Bag from <code>MultiValuedMap</code> in a null-safe manner.
     *
     * @param <K> the key type
     * @param <V> the value type
     * @param map  the {@link MultiValuedMap} to use
     * @param key  the key to look up
     * @return the Collection in the {@link MultiValuedMap} as Bag, or null if input map is null
     */
    public static <K, V> Bag<V> getValuesAsBag(final MultiValuedMap<K, V> map, final K key) {
        if (map != null) {
            final Collection<V> col = map.get(key);
            if (col instanceof Bag) {
                return (Bag<V>) col;
            }
            return new HashBag<>(col);
        }
        return null;
    }

    // Factory Methods
    // -----------------------------------------------------------------------

    /**
     * Creates a {@link ListValuedMap} with an {@link java.util.ArrayList ArrayList} as
     * collection class to store the values mapped to a key.
     *
     * @param <K> the key type
     * @param <V> the value type
     * @return a new <code>ListValuedMap</code>
     */
    public static <K, V> ListValuedMap<K, V> newListValuedHashMap() {
        return new ArrayListValuedHashMap<>();
    }

    /**
     * Creates a {@link SetValuedMap} with an {@link java.util.HashSet HashSet} as
     * collection class to store the values mapped to a key.
     *
     * @param <K> the key type
     * @param <V> the value type
     * @return a new {@link SetValuedMap}
     */
    public static <K, V> SetValuedMap<K, V> newSetValuedHashMap() {
        return new HashSetValuedHashMap<>();
    }

    // MultiValuedMap Decorators
    // -----------------------------------------------------------------------

    /**
     * Returns an <code>UnmodifiableMultiValuedMap</code> backed by the given
     * map.
     *
     * @param <K> the key type
     * @param <V> the value type
     * @param map  the {@link MultiValuedMap} to decorate, must not be null
     * @return an unmodifiable {@link MultiValuedMap} backed by the provided map
     * @throws NullPointerException if map is null
     */
    public static <K, V> MultiValuedMap<K, V> unmodifiableMultiValuedMap(
            final MultiValuedMap<? extends K, ? extends V> map) {
        return UnmodifiableMultiValuedMap.<K, V>unmodifiableMultiValuedMap(map);
    }

    /**
     * Returns a <code>TransformedMultiValuedMap</code> backed by the given map.
     * <p>
     * This method returns a new <code>MultiValuedMap</code> (decorating the
     * specified map) that will transform any new entries added to it. Existing
     * entries in the specified map will not be transformed. If you want that
     * behaviour, see {@link TransformedMultiValuedMap#transformedMap}.
     * <p>
     * Each object is passed through the transformers as it is added to the Map.
     * It is important not to use the original map after invoking this method,
     * as it is a back door for adding untransformed objects.
     * <p>
     * If there are any elements already in the map being decorated, they are
     * NOT transformed.
     *
     * @param <K> the key type
     * @param <V> the value type
     * @param map  the {@link MultiValuedMap} to transform, must not be null, typically empty
     * @param keyTransformer  the transformer for the map keys, null means no transformation
     * @param valueTransformer  the transformer for the map values, null means no transformation
     * @return a transformed <code>MultiValuedMap</code> backed by the given map
     * @throws NullPointerException if map is null
     */
    public static <K, V> MultiValuedMap<K, V> transformedMultiValuedMap(final MultiValuedMap<K, V> map,
            final Transformer<? super K, ? extends K> keyTransformer,
            final Transformer<? super V, ? extends V> valueTransformer) {
        return TransformedMultiValuedMap.transformingMap(map, keyTransformer, valueTransformer);
    }

}
