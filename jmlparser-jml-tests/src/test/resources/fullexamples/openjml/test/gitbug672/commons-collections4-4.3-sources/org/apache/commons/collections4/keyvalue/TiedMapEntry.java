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
package org.apache.commons.collections4.keyvalue;

import java.io.Serializable;
import java.util.Map;

import org.apache.commons.collections4.KeyValue;

/**
 * A {@link java.util.Map.Entry Map.Entry} tied to a map underneath.
 * <p>
 * This can be used to enable a map entry to make changes on the underlying
 * map, however this will probably mess up any iterators.
 *
 * @since 3.0
 */
public class TiedMapEntry<K, V> implements Map.Entry<K, V>, KeyValue<K, V>, Serializable {

    /** Serialization version */
    private static final long serialVersionUID = -8453869361373831205L;

    /** The map underlying the entry/iterator */
    private final Map<K, V> map;

    /** The key */
    private final K key;

    /**
     * Constructs a new entry with the given Map and key.
     *
     * @param map  the map
     * @param key  the key
     */
    public TiedMapEntry(final Map<K, V> map, final K key) {
        super();
        this.map = map;
        this.key = key;
    }

    // Map.Entry interface
    //-------------------------------------------------------------------------
    /**
     * Gets the key of this entry
     *
     * @return the key
     */
    @Override
    public K getKey() {
        return key;
    }

    /**
     * Gets the value of this entry direct from the map.
     *
     * @return the value
     */
    @Override
    public V getValue() {
        return map.get(key);
    }

    /**
     * Sets the value associated with the key direct onto the map.
     *
     * @param value  the new value
     * @return the old value
     * @throws IllegalArgumentException if the value is set to this map entry
     */
    @Override
    public V setValue(final V value) {
        if (value == this) {
            throw new IllegalArgumentException("Cannot set value to this map entry");
        }
        return map.put(key, value);
    }

    /**
     * Compares this <code>Map.Entry</code> with another <code>Map.Entry</code>.
     * <p>
     * Implemented per API documentation of {@link java.util.Map.Entry#equals(Object)}
     *
     * @param obj  the object to compare to
     * @return true if equal key and value
     */
    @Override
    public boolean equals(final Object obj) {
        if (obj == this) {
            return true;
        }
        if (obj instanceof Map.Entry == false) {
            return false;
        }
        final Map.Entry<?,?> other = (Map.Entry<?,?>) obj;
        final Object value = getValue();
        return
            (key == null ? other.getKey() == null : key.equals(other.getKey())) &&
            (value == null ? other.getValue() == null : value.equals(other.getValue()));
    }

    /**
     * Gets a hashCode compatible with the equals method.
     * <p>
     * Implemented per API documentation of {@link java.util.Map.Entry#hashCode()}
     *
     * @return a suitable hash code
     */
    @Override
    public int hashCode() {
        final Object value = getValue();
        return (getKey() == null ? 0 : getKey().hashCode()) ^
               (value == null ? 0 : value.hashCode());
    }

    /**
     * Gets a string version of the entry.
     *
     * @return entry as a string
     */
    @Override
    public String toString() {
        return getKey() + "=" + getValue();
    }

}
