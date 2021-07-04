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

import java.io.Serializable;

import java.util.Collection;
import java.util.Map;
import java.util.Set;

import org.apache.commons.collections4.set.CompositeSet;
import org.apache.commons.collections4.CollectionUtils;
import org.apache.commons.collections4.collection.CompositeCollection;

/**
 * Decorates a map of other maps to provide a single unified view.
 * <p>
 * Changes made to this map will actually be made on the decorated map.
 * Add and remove operations require the use of a pluggable strategy. If no
 * strategy is provided then add and remove are unsupported.
 * <p>
 * <strong>Note that CompositeMap is not synchronized and is not thread-safe.</strong>
 * If you wish to use this map from multiple threads concurrently, you must use
 * appropriate synchronization. The simplest approach is to wrap this map
 * using {@link java.util.Collections#synchronizedMap(Map)}. This class may throw
 * exceptions when accessed by concurrent threads without synchronization.
 *
 * @param <K> the type of the keys in this map
 * @param <V> the type of the values in this map
 * @since 3.0
 */
public class CompositeMap<K, V> extends AbstractIterableMap<K, V> implements Serializable {

    /** Serialization version */
    private static final long serialVersionUID = -6096931280583808322L;

    /** Array of all maps in the composite */
    private Map<K, V>[] composite;

    /** Handle mutation operations */
    private MapMutator<K, V> mutator;

    /**
     * Create a new, empty, CompositeMap.
     */
    @SuppressWarnings("unchecked")
    public CompositeMap() {
        this(new Map[] {}, null);
    }

    /**
     * Create a new CompositeMap with two composited Map instances.
     *
     * @param one  the first Map to be composited
     * @param two  the second Map to be composited
     * @throws IllegalArgumentException if there is a key collision
     */
    @SuppressWarnings("unchecked")
    public CompositeMap(final Map<K, V> one, final Map<K, V> two) {
        this(new Map[] { one, two }, null);
    }

    /**
     * Create a new CompositeMap with two composited Map instances.
     *
     * @param one  the first Map to be composited
     * @param two  the second Map to be composited
     * @param mutator  MapMutator to be used for mutation operations
     */
    @SuppressWarnings("unchecked")
    public CompositeMap(final Map<K, V> one, final Map<K, V> two, final MapMutator<K, V> mutator) {
        this(new Map[] { one, two }, mutator);
    }

    /**
     * Create a new CompositeMap which composites all of the Map instances in the
     * argument. It copies the argument array, it does not use it directly.
     *
     * @param composite  the Maps to be composited
     * @throws IllegalArgumentException if there is a key collision
     */
    public CompositeMap(final Map<K, V>... composite) {
        this(composite, null);
    }

    /**
     * Create a new CompositeMap which composites all of the Map instances in the
     * argument. It copies the argument array, it does not use it directly.
     *
     * @param composite  Maps to be composited
     * @param mutator  MapMutator to be used for mutation operations
     */
    @SuppressWarnings("unchecked")
    public CompositeMap(final Map<K, V>[] composite, final MapMutator<K, V> mutator) {
        this.mutator = mutator;
        this.composite = new Map[0];
        for (int i = composite.length - 1; i >= 0; --i) {
            this.addComposited(composite[i]);
        }
    }

    //-----------------------------------------------------------------------
    /**
     * Specify the MapMutator to be used by mutation operations.
     *
     * @param mutator  the MapMutator to be used for mutation delegation
     */
    public void setMutator(final MapMutator<K, V> mutator) {
        this.mutator = mutator;
    }

    /**
     * Add an additional Map to the composite.
     *
     * @param map  the Map to be added to the composite
     * @throws IllegalArgumentException if there is a key collision and there is no
     *         MapMutator set to handle it.
     */
    @SuppressWarnings("unchecked")
    public synchronized void addComposited(final Map<K, V> map) throws IllegalArgumentException {
        for (int i = composite.length - 1; i >= 0; --i) {
            final Collection<K> intersect = CollectionUtils.intersection(this.composite[i].keySet(), map.keySet());
            if (intersect.size() != 0) {
                if (this.mutator == null) {
                    throw new IllegalArgumentException("Key collision adding Map to CompositeMap");
                }
                this.mutator.resolveCollision(this, this.composite[i], map, intersect);
            }
        }
        final Map<K, V>[] temp = new Map[this.composite.length + 1];
        System.arraycopy(this.composite, 0, temp, 0, this.composite.length);
        temp[temp.length - 1] = map;
        this.composite = temp;
    }

    /**
     * Remove a Map from the composite.
     *
     * @param map  the Map to be removed from the composite
     * @return The removed Map or <code>null</code> if map is not in the composite
     */
    @SuppressWarnings("unchecked")
    public synchronized Map<K, V> removeComposited(final Map<K, V> map) {
        final int size = this.composite.length;
        for (int i = 0; i < size; ++i) {
            if (this.composite[i].equals(map)) {
                final Map<K, V>[] temp = new Map[size - 1];
                System.arraycopy(this.composite, 0, temp, 0, i);
                System.arraycopy(this.composite, i + 1, temp, i, size - i - 1);
                this.composite = temp;
                return map;
            }
        }
        return null;
    }

    //-----------------------------------------------------------------------
    /**
     * Calls <code>clear()</code> on all composited Maps.
     *
     * @throws UnsupportedOperationException if any of the composited Maps do not support clear()
     */
    @Override
    public void clear() {
        for (int i = this.composite.length - 1; i >= 0; --i) {
            this.composite[i].clear();
        }
    }

    /**
     * Returns {@code true} if this map contains a mapping for the specified
     * key.  More formally, returns {@code true} if and only if
     * this map contains at a mapping for a key {@code k} such that
     * {@code (key==null ? k==null : key.equals(k))}.  (There can be
     * at most one such mapping.)
     *
     * @param key  key whose presence in this map is to be tested.
     * @return {@code true} if this map contains a mapping for the specified
     *         key.
     *
     * @throws ClassCastException if the key is of an inappropriate type for
     *         this map (optional).
     * @throws NullPointerException if the key is {@code null} and this map
     *            does not not permit {@code null} keys (optional).
     */
    @Override
    public boolean containsKey(final Object key) {
        for (int i = this.composite.length - 1; i >= 0; --i) {
            if (this.composite[i].containsKey(key)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Returns {@code true} if this map maps one or more keys to the
     * specified value.  More formally, returns {@code true} if and only if
     * this map contains at least one mapping to a value {@code v} such that
     * {@code (value==null ? v==null : value.equals(v))}.  This operation
     * will probably require time linear in the map size for most
     * implementations of the {@code Map} interface.
     *
     * @param value value whose presence in this map is to be tested.
     * @return {@code true} if this map maps one or more keys to the
     *         specified value.
     * @throws ClassCastException if the value is of an inappropriate type for
     *         this map (optional).
     * @throws NullPointerException if the value is {@code null} and this map
     *            does not not permit {@code null} values (optional).
     */
    @Override
    public boolean containsValue(final Object value) {
        for (int i = this.composite.length - 1; i >= 0; --i) {
            if (this.composite[i].containsValue(value)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Returns a set view of the mappings contained in this map.  Each element
     * in the returned set is a <code>Map.Entry</code>.  The set is backed by the
     * map, so changes to the map are reflected in the set, and vice-versa.
     * If the map is modified while an iteration over the set is in progress,
     * the results of the iteration are undefined.  The set supports element
     * removal, which removes the corresponding mapping from the map, via the
     * {@code Iterator.remove}, {@code Set.remove}, {@code removeAll},
     * {@code retainAll} and {@code clear} operations.  It does not support
     * the {@code add} or {@code addAll} operations.
     * <p>
     * This implementation returns a <code>CompositeSet</code> which
     * composites the entry sets from all of the composited maps.
     *
     * @see CompositeSet
     * @return a set view of the mappings contained in this map.
     */
    @Override
    public Set<Map.Entry<K, V>> entrySet() {
        final CompositeSet<Map.Entry<K, V>> entries = new CompositeSet<>();
        for (int i = composite.length - 1; i >= 0; --i) {
            entries.addComposited(composite[i].entrySet());
        }
        return entries;
    }

    /**
     * Returns the value to which this map maps the specified key.  Returns
     * {@code null} if the map contains no mapping for this key.  A return
     * value of {@code null} does not <i>necessarily</i> indicate that the
     * map contains no mapping for the key; it's also possible that the map
     * explicitly maps the key to {@code null}.  The {@code containsKey}
     * operation may be used to distinguish these two cases.
     *
     * <p>More formally, if this map contains a mapping from a key
     * {@code k} to a value {@code v} such that <code>(key==null ? k==null :
     * key.equals(k))</code>, then this method returns {@code v}; otherwise
     * it returns {@code null}.  (There can be at most one such mapping.)
     *
     * @param key key whose associated value is to be returned.
     * @return the value to which this map maps the specified key, or
     *         {@code null} if the map contains no mapping for this key.
     *
     * @throws ClassCastException if the key is of an inappropriate type for
     *         this map (optional).
     * @throws NullPointerException key is {@code null} and this map does not
     *         not permit {@code null} keys (optional).
     *
     * @see #containsKey(Object)
     */
    @Override
    public V get(final Object key) {
        for (int i = this.composite.length - 1; i >= 0; --i) {
            if (this.composite[i].containsKey(key)) {
                return this.composite[i].get(key);
            }
        }
        return null;
    }

    /**
     * Returns {@code true} if this map contains no key-value mappings.
     *
     * @return {@code true} if this map contains no key-value mappings.
     */
    @Override
    public boolean isEmpty() {
        for (int i = this.composite.length - 1; i >= 0; --i) {
            if (!this.composite[i].isEmpty()) {
                return false;
            }
        }
        return true;
    }

    /**
     * Returns a set view of the keys contained in this map.  The set is
     * backed by the map, so changes to the map are reflected in the set, and
     * vice-versa.  If the map is modified while an iteration over the set is
     * in progress, the results of the iteration are undefined.  The set
     * supports element removal, which removes the corresponding mapping from
     * the map, via the {@code Iterator.remove}, {@code Set.remove},
     * {@code removeAll} {@code retainAll}, and {@code clear} operations.
     * It does not support the add or {@code addAll} operations.
     * <p>
     * This implementation returns a <code>CompositeSet</code> which
     * composites the key sets from all of the composited maps.
     *
     * @return a set view of the keys contained in this map.
     */
    @Override
    public Set<K> keySet() {
        final CompositeSet<K> keys = new CompositeSet<>();
        for (int i = this.composite.length - 1; i >= 0; --i) {
            keys.addComposited(this.composite[i].keySet());
        }
        return keys;
    }

    /**
     * Associates the specified value with the specified key in this map
     * (optional operation).  If the map previously contained a mapping for
     * this key, the old value is replaced by the specified value.  (A map
     * {@code m} is said to contain a mapping for a key {@code k} if and only
     * if {@link #containsKey(Object) m.containsKey(k)} would return
     * {@code true}.))
     *
     * @param key key with which the specified value is to be associated.
     * @param value value to be associated with the specified key.
     * @return previous value associated with specified key, or {@code null}
     *         if there was no mapping for key.  A {@code null} return can
     *         also indicate that the map previously associated {@code null}
     *         with the specified key, if the implementation supports
     *         {@code null} values.
     *
     * @throws UnsupportedOperationException if no MapMutator has been specified
     * @throws ClassCastException if the class of the specified key or value
     *            prevents it from being stored in this map.
     * @throws IllegalArgumentException if some aspect of this key or value
     *            prevents it from being stored in this map.
     * @throws NullPointerException this map does not permit {@code null}
     *            keys or values, and the specified key or value is
     *            {@code null}.
     */
    @Override
    public V put(final K key, final V value) {
        if (this.mutator == null) {
            throw new UnsupportedOperationException("No mutator specified");
        }
        return this.mutator.put(this, this.composite, key, value);
    }

    /**
     * Copies all of the mappings from the specified map to this map
     * (optional operation).  The effect of this call is equivalent to that
     * of calling {@link #put(Object,Object) put(k, v)} on this map once
     * for each mapping from key {@code k} to value {@code v} in the
     * specified map.  The behavior of this operation is unspecified if the
     * specified map is modified while the operation is in progress.
     *
     * @param map Mappings to be stored in this map.
     *
     * @throws UnsupportedOperationException if the {@code putAll} method is
     *         not supported by this map.
     *
     * @throws ClassCastException if the class of a key or value in the
     *         specified map prevents it from being stored in this map.
     *
     * @throws IllegalArgumentException some aspect of a key or value in the
     *         specified map prevents it from being stored in this map.
     * @throws NullPointerException the specified map is {@code null}, or if
     *         this map does not permit {@code null} keys or values, and the
     *         specified map contains {@code null} keys or values.
     */
    @Override
    public void putAll(final Map<? extends K, ? extends V> map) {
        if (this.mutator == null) {
            throw new UnsupportedOperationException("No mutator specified");
        }
        this.mutator.putAll(this, this.composite, map);
    }

    /**
     * Removes the mapping for this key from this map if it is present
     * (optional operation).   More formally, if this map contains a mapping
     * from key {@code k} to value {@code v} such that
     * <code>(key==null ?  k==null : key.equals(k))</code>, that mapping
     * is removed.  (The map can contain at most one such mapping.)
     *
     * <p>Returns the value to which the map previously associated the key, or
     * {@code null} if the map contained no mapping for this key.  (A
     * {@code null} return can also indicate that the map previously
     * associated {@code null} with the specified key if the implementation
     * supports {@code null} values.)  The map will not contain a mapping for
     * the specified  key once the call returns.
     *
     * @param key key whose mapping is to be removed from the map.
     * @return previous value associated with specified key, or {@code null}
     *         if there was no mapping for key.
     *
     * @throws ClassCastException if the key is of an inappropriate type for
     *         the composited map (optional).
     * @throws NullPointerException if the key is {@code null} and the composited map
     *            does not not permit {@code null} keys (optional).
     * @throws UnsupportedOperationException if the {@code remove} method is
     *         not supported by the composited map containing the key
     */
    @Override
    public V remove(final Object key) {
        for (int i = this.composite.length - 1; i >= 0; --i) {
            if (this.composite[i].containsKey(key)) {
                return this.composite[i].remove(key);
            }
        }
        return null;
    }

    /**
     * Returns the number of key-value mappings in this map.  If the
     * map contains more than {@code Integer.MAX_VALUE} elements, returns
     * {@code Integer.MAX_VALUE}.
     *
     * @return the number of key-value mappings in this map.
     */
    @Override
    public int size() {
        int size = 0;
        for (int i = this.composite.length - 1; i >= 0; --i) {
            size += this.composite[i].size();
        }
        return size;
    }

    /**
     * Returns a collection view of the values contained in this map.  The
     * collection is backed by the map, so changes to the map are reflected in
     * the collection, and vice-versa.  If the map is modified while an
     * iteration over the collection is in progress, the results of the
     * iteration are undefined.  The collection supports element removal,
     * which removes the corresponding mapping from the map, via the
     * {@code Iterator.remove}, {@code Collection.remove},
     * {@code removeAll}, {@code retainAll} and {@code clear} operations.
     * It does not support the add or {@code addAll} operations.
     *
     * @return a collection view of the values contained in this map.
     */
    @Override
    public Collection<V> values() {
        final CompositeCollection<V> values = new CompositeCollection<>();
        for (int i = composite.length - 1; i >= 0; --i) {
            values.addComposited(composite[i].values());
        }
        return values;
    }

    /**
     * Checks if this Map equals another as per the Map specification.
     *
     * @param obj  the object to compare to
     * @return true if the maps are equal
     */
    @Override
    public boolean equals(final Object obj) {
        if (obj instanceof Map) {
            final Map<?, ?> map = (Map<?, ?>) obj;
            return this.entrySet().equals(map.entrySet());
        }
        return false;
    }

    /**
     * Gets a hash code for the Map as per the Map specification.
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        int code = 0;
        for (final Map.Entry<K, V> entry : entrySet()) {
            code += entry.hashCode();
        }
        return code;
    }

    /**
     * This interface allows definition for all of the indeterminate
     * mutators in a CompositeMap, as well as providing a hook for
     * callbacks on key collisions.
     *
     * @param <K> the type of the keys in the map
     * @param <V> the type of the values in the map
     */
    public interface MapMutator<K, V> extends Serializable {
        /**
         * Called when adding a new Composited Map results in a
         * key collision.
         *
         * @param composite  the CompositeMap with the collision
         * @param existing  the Map already in the composite which contains the
         *        offending key
         * @param added  the Map being added
         * @param intersect  the intersection of the keysets of the existing and added maps
         */
        void resolveCollision(CompositeMap<K, V> composite, Map<K, V> existing,
                Map<K, V> added, Collection<K> intersect);

        /**
         * Called when the CompositeMap.put() method is invoked.
         *
         * @param map  the CompositeMap which is being modified
         * @param composited  array of Maps in the CompositeMap being modified
         * @param key  key with which the specified value is to be associated.
         * @param value  value to be associated with the specified key.
         * @return previous value associated with specified key, or {@code null}
         *         if there was no mapping for key.  A {@code null} return can
         *         also indicate that the map previously associated {@code null}
         *         with the specified key, if the implementation supports
         *         {@code null} values.
         *
         * @throws UnsupportedOperationException if not defined
         * @throws ClassCastException if the class of the specified key or value
         *            prevents it from being stored in this map.
         * @throws IllegalArgumentException if some aspect of this key or value
         *            prevents it from being stored in this map.
         * @throws NullPointerException this map does not permit {@code null}
         *            keys or values, and the specified key or value is
         *            {@code null}.
         */
        V put(CompositeMap<K, V> map, Map<K, V>[] composited, K key, V value);

        /**
         * Called when the CompositeMap.putAll() method is invoked.
         *
         * @param map  the CompositeMap which is being modified
         * @param composited  array of Maps in the CompositeMap being modified
         * @param mapToAdd  Mappings to be stored in this CompositeMap
         *
         * @throws UnsupportedOperationException if not defined
         * @throws ClassCastException if the class of the specified key or value
         *            prevents it from being stored in this map.
         * @throws IllegalArgumentException if some aspect of this key or value
         *            prevents it from being stored in this map.
         * @throws NullPointerException this map does not permit {@code null}
         *            keys or values, and the specified key or value is
         *            {@code null}.
         */
        void putAll(CompositeMap<K, V> map, Map<K, V>[] composited,
                Map<? extends K, ? extends V> mapToAdd);
    }
}
