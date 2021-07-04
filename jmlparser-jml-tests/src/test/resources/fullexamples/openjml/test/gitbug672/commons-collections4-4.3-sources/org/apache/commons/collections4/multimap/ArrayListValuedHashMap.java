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

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import org.apache.commons.collections4.MultiValuedMap;

/**
 * Implements a {@code ListValuedMap}, using a {@link HashMap} to provide data
 * storage and {@link ArrayList}s as value collections. This is the standard
 * implementation of a ListValuedMap.
 * <p>
 * <strong>Note that ArrayListValuedHashMap is not synchronized and is not
 * thread-safe.</strong> If you wish to use this map from multiple threads
 * concurrently, you must use appropriate synchronization. This class may throw
 * exceptions when accessed by concurrent threads without synchronization.
 *
 * @param <K> the type of the keys in this map
 * @param <V> the type of the values in this map
 * @since 4.1
 */
public class ArrayListValuedHashMap<K, V> extends AbstractListValuedMap<K, V>
    implements Serializable {

    /** Serialization Version */
    private static final long serialVersionUID = 20151118L;

    /**
     * The initial map capacity used when none specified in constructor.
     */
    private static final int DEFAULT_INITIAL_MAP_CAPACITY = 16;

    /**
     * The initial list capacity when using none specified in constructor.
     */
    private static final int DEFAULT_INITIAL_LIST_CAPACITY = 3;

    /**
     * The initial list capacity when creating a new value collection.
     */
    private final int initialListCapacity;

    /**
     * Creates an empty ArrayListValuedHashMap with the default initial
     * map capacity (16) and the default initial list capacity (3).
     */
    public ArrayListValuedHashMap() {
        this(DEFAULT_INITIAL_MAP_CAPACITY, DEFAULT_INITIAL_LIST_CAPACITY);
    }

    /**
     * Creates an empty ArrayListValuedHashMap with the default initial
     * map capacity (16) and the specified initial list capacity.
     *
     * @param initialListCapacity  the initial capacity used for value collections
     */
    public ArrayListValuedHashMap(final int initialListCapacity) {
        this(DEFAULT_INITIAL_MAP_CAPACITY, initialListCapacity);
    }

    /**
     * Creates an empty ArrayListValuedHashMap with the specified initial
     * map and list capacities.
     *
     * @param initialMapCapacity  the initial hashmap capacity
     * @param initialListCapacity  the initial capacity used for value collections
     */
    public ArrayListValuedHashMap(final int initialMapCapacity, final int initialListCapacity) {
        super(new HashMap<K, ArrayList<V>>(initialMapCapacity));
        this.initialListCapacity = initialListCapacity;
    }

    /**
     * Creates an ArrayListValuedHashMap copying all the mappings of the given map.
     *
     * @param map a <code>MultiValuedMap</code> to copy into this map
     */
    public ArrayListValuedHashMap(final MultiValuedMap<? extends K, ? extends V> map) {
        this(map.size(), DEFAULT_INITIAL_LIST_CAPACITY);
        super.putAll(map);
    }

    /**
     * Creates an ArrayListValuedHashMap copying all the mappings of the given map.
     *
     * @param map a <code>Map</code> to copy into this map
     */
    public ArrayListValuedHashMap(final Map<? extends K, ? extends V> map) {
        this(map.size(), DEFAULT_INITIAL_LIST_CAPACITY);
        super.putAll(map);
    }

    // -----------------------------------------------------------------------
    @Override
    protected ArrayList<V> createCollection() {
        return new ArrayList<>(initialListCapacity);
    }

    // -----------------------------------------------------------------------
    /**
     * Trims the capacity of all value collections to their current size.
     */
    public void trimToSize() {
        for (final Collection<V> coll : getMap().values()) {
            final ArrayList<V> list = (ArrayList<V>) coll;
            list.trimToSize();
        }
    }

    // -----------------------------------------------------------------------
    private void writeObject(final ObjectOutputStream oos) throws IOException {
        oos.defaultWriteObject();
        doWriteObject(oos);
    }

    private void readObject(final ObjectInputStream ois) throws IOException, ClassNotFoundException {
        ois.defaultReadObject();
        setMap(new HashMap<K, ArrayList<V>>());
        doReadObject(ois);
    }

}
