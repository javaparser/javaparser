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
import java.util.Map.Entry;
import java.util.Set;

/**
 * Defines a map that holds a collection of values against each key.
 * <p>
 * A {@code MultiValuedMap} is a Map with slightly different semantics:
 * <ul>
 *   <li>Putting a value into the map will add the value to a {@link Collection} at that key.</li>
 *   <li>Getting a value will return a {@link Collection}, holding all the values put to that key.</li>
 * </ul>
 * <p>
 * For example:
 * <pre>
 * MultiValuedMap&lt;K, String&gt; map = new MultiValuedHashMap&lt;K, String&gt;();
 * map.put(key, &quot;A&quot;);
 * map.put(key, &quot;B&quot;);
 * map.put(key, &quot;C&quot;);
 * Collection&lt;String&gt; coll = map.get(key);
 * </pre>
 * <p>
 * <code>coll</code> will be a collection containing "A", "B", "C".
 * <p>
 *
 * @param <K> the type of the keys in this map
 * @param <V> the type of the values in this map
 * @since 4.1
 */
public interface MultiValuedMap<K, V> {
    // Query operations

    /**
     * Gets the total size of the map.
     * <p>
     * Implementations would return the total size of the map which is the count
     * of the values from all keys.
     *
     * @return the total size of the map
     */
    int size();

    /**
     * Returns {@code true} if this map contains no key-value mappings.
     *
     * @return {@code true} if this map contains no key-value mappings
     */
    boolean isEmpty();

    /**
     * Returns {@code true} if this map contains a mapping for the specified
     * key. More formally, returns {@code true} if and only if this map contains
     * a mapping for a key {@code k} such that {@code (key==null ? k==null : key.equals(k))}.
     * (There can be at most one such mapping.)
     *
     * @param key  key whose presence in this map is to be tested
     * @return true if this map contains a mapping for the specified key
     * @throws NullPointerException if the specified key is null and this map
     *   does not permit null keys (optional)
     */
    boolean containsKey(Object key);

    /**
     * Checks whether the map contains at least one mapping for the specified value.
     *
     * @param value  the value to search for
     * @return true if the map contains the value
     * @throws NullPointerException if the value is null and null values are not supported
     *   by the used collection types (optional)
     */
    boolean containsValue(Object value);

    /**
     * Checks whether the map contains a mapping for the specified key and value.
     *
     * @param key  the key to search for
     * @param value  the value to search for
     * @return true if the map contains the value
     */
    boolean containsMapping(Object key, Object value);

    /**
     * Returns a view collection of the values associated with the specified key.
     * <p>
     * This method will return an <b>empty</b> collection if {@link #containsKey(Object)}
     * returns {@code false}. Changes to the returned collection will update the underlying
     * {@code MultiValuedMap} and vice-versa.
     *
     * @param key  the key to retrieve
     * @return the {@code Collection} of values, implementations should
     *   return an empty collection for no mapping
     * @throws NullPointerException if the key is null and null keys are invalid (optional)
     */
    Collection<V> get(K key);

    // Modification operations

    /**
     * Adds a key-value mapping to this multi-valued map.
     * <p>
     * Unlike a normal {@code Map} the previous value is not replaced.
     * Instead the new value is added to the collection stored against the key.
     * Depending on the collection type used, duplicate key-value mappings may
     * be allowed.
     * <p>
     * The method will return {@code true} if the size of the multi-valued map
     * has been increased because of this operation.
     *
     * @param key  the key to store against
     * @param value  the value to add to the collection at the key
     * @return true if the map changed as a result of this put operation, or false
     *   if the map already contained the key-value mapping and the collection
     *   type does not allow duplicate values, e.g. when using a Set
     * @throws UnsupportedOperationException if the put operation is not supported by
     *   this multi-valued map, e.g. if it is unmodifiable
     * @throws NullPointerException if the key or value is null and null is invalid (optional)
     * @throws IllegalArgumentException if some aspect of the specified key or value prevents
     *   it from being stored in this multi-valued map
     */
    boolean put(K key, V value);

    /**
     * Adds a mapping to the specified key for all values contained in the given Iterable.
     *
     * @param key  the key to store against
     * @param values  the values to add to the collection at the key, may not be null
     * @return true if the map changed as a result of this operation
     * @throws NullPointerException if the specified iterable is null, or if this map
     *   does not permit null keys or values, and the specified key or values contain
     *   null (optional)
     */
    boolean putAll(K key, Iterable<? extends V> values);

    /**
     * Copies all mappings from the specified map to this multi-valued map
     * (optional operation).
     * <p>
     * The effect of this call is equivalent to that of calling
     * {@link #put(Object,Object) put(k, v)} on this map once for each mapping
     * from key {@code k} to value {@code v} in the specified map.
     * <p>
     * The behavior of this operation is undefined if the specified map is modified
     * while the operation is in progress.
     *
     * @param map  mappings to be stored in this map, may not be null
     * @return true if the map changed as a result of this operation
     * @throws UnsupportedOperationException if the {@code putAll} operation is
     *   not supported by this map
     * @throws NullPointerException if the specified map is null, or if this map
     *   does not permit null keys or values, and the specified map
     *   contains null keys or values (optional)
     * @throws IllegalArgumentException if some property of a key or value in
     *   the specified map prevents it from being stored in this map
     */
    boolean putAll(Map<? extends K, ? extends V> map);

    /**
     * Copies all mappings from the specified map to this multi-valued map
     * (optional operation).
     * <p>
     * The effect of this call is equivalent to that of calling
     * {@link #put(Object,Object) put(k, v)} on this map once for each
     * mapping from key {@code k} to value {@code v} in the specified map.
     * <p>
     * The behavior of this operation is undefined if the specified map is modified
     * while the operation is in progress.
     *
     * @param map  mappings to be stored in this map, may not be null
     * @return true if the map changed as a result of this operation
     * @throws UnsupportedOperationException if the {@code putAll} operation is
     *   not supported by this map
     * @throws NullPointerException if the specified map is null, or if this map
     *   does not permit null keys or values, and the specified map
     *   contains null keys or values (optional)
     * @throws IllegalArgumentException if some property of a key or value in
     *   the specified map prevents it from being stored in this map
     */
    boolean putAll(MultiValuedMap<? extends K, ? extends V> map);

    /**
     * Removes all values associated with the specified key.
     * <p>
     * The returned collection <i>may</i> be modifiable, but updates will not be propagated
     * to this multi-valued map. In case no mapping was stored for the specified
     * key, an empty, unmodifiable collection will be returned.
     *
     * @param key  the key to remove values from
     * @return the values that were removed
     * @throws UnsupportedOperationException if the map is unmodifiable
     * @throws NullPointerException if the key is null and null keys are invalid (optional)
     */
    Collection<V> remove(Object key);

    /**
     * Removes a key-value mapping from the map.
     * <p>
     * The item is removed from the collection mapped to the specified key.
     * Other values attached to that key are unaffected.
     * <p>
     * If the last value for a key is removed, implementations typically return
     * an empty collection from a subsequent <code>get(Object)</code>.
     *
     * @param key  the key to remove from
     * @param item  the item to remove
     * @return true if the mapping was removed, false otherwise
     * @throws UnsupportedOperationException if the map is unmodifiable
     * @throws NullPointerException if the key or value is null and null is invalid (optional)
     */
    boolean removeMapping(Object key, Object item);

    /**
     * Removes all of the mappings from this map (optional operation).
     * <p>
     * The map will be empty after this call returns.
     *
     * @throws UnsupportedOperationException if the map is unmodifiable
     */
    void clear();

    // Views

    /**
     * Returns a {@link Collection} view of the mappings contained in this multi-valued map.
     * <p>
     * The collection is backed by the map, so changes to the map are reflected
     * in the collection, and vice-versa.
     *
     * @return a set view of the mappings contained in this map
     */
    Collection<Entry<K, V>> entries();

    /**
     * Returns a {@link MultiSet} view of the keys contained in this multi-valued map.
     * <p>
     * The {@link MultiSet#getCount(Object)} method of the returned multiset will give
     * the same result a calling {@code get(Object).size()} for the same key.
     * <p>
     * This multiset is backed by the map, so any changes in the map are reflected in
     * the multiset.
     *
     * @return a multiset view of the keys contained in this map
     */
    MultiSet<K> keys();

    /**
     * Returns a {@link Set} view of the keys contained in this multi-valued map.
     * <p>
     * The set is backed by the map, so changes to the map are reflected
     * in the set, and vice-versa.
     * <p>
     * If the map is modified while an iteration over the set is in
     * progress (except through the iterator's own {@code remove} operation),
     * the result of the iteration is undefined. The set supports element
     * removal, which removes the corresponding mapping from the map, via the
     * {@code Iterator.remove}, {@code Set.remove}, {@code removeAll},
     * {@code retainAll}, and {@code clear} operations. It does not support
     * the {@code add} or {@code addAll} operations.
     *
     * @return a set view of the keys contained in this map
     */
    Set<K> keySet();

    /**
     * Gets a {@link Collection} view of all values contained in this multi-valued map.
     * <p>
     * Implementations typically return a collection containing the combination
     * of values from all keys.
     *
     * @return a collection view of the values contained in this multi-valued map
     */
    Collection<V> values();

    /**
     * Returns a view of this multi-valued map as a {@code Map} from each distinct
     * key to the non-empty collection of that key's associated values.
     * <p>
     * Note that {@code this.asMap().get(k)} is equivalent to {@code this.get(k)}
     * only when {@code k} is a key contained in the multi-valued map; otherwise it
     * returns {@code null} as opposed to an empty collection.
     * <p>
     * Changes to the returned map or the collections that serve as its values
     * will update the underlying multi-valued map, and vice versa. The map does
     * not support {@code put} or {@code putAll}, nor do its entries support
     * {@link java.util.Map.Entry#setValue(Object) setValue}.
     *
     * @return a map view of the mappings in this multi-valued map
     */
    Map<K, Collection<V>> asMap();

    // Iterators

    /**
     * Obtains a <code>MapIterator</code> over this multi-valued map.
     * <p>
     * A map iterator is an efficient way of iterating over maps. There is no
     * need to access the entries collection or use {@code Map.Entry} objects.
     *
     * @return a map iterator
     */
    MapIterator<K, V> mapIterator();

}
