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

/**
 * Defines a map that maintains order and allows both forward and backward
 * iteration through that order.
 *
 * @param <K> the type of the keys in the map
 * @param <V> the type of the values in the map
 *
 * @since 3.0
 */
public interface OrderedMap<K, V> extends IterableMap<K, V> {

    /**
     * Obtains an <code>OrderedMapIterator</code> over the map.
     * <p>
     * A ordered map iterator is an efficient way of iterating over maps
     * in both directions.
     *
     * @return a map iterator
     */
    @Override
    OrderedMapIterator<K, V> mapIterator();

    /**
     * Gets the first key currently in this map.
     *
     * @return the first key currently in this map
     * @throws java.util.NoSuchElementException if this map is empty
     */
    K firstKey();

    /**
     * Gets the last key currently in this map.
     *
     * @return the last key currently in this map
     * @throws java.util.NoSuchElementException if this map is empty
     */
    K lastKey();

    /**
     * Gets the next key after the one specified.
     *
     * @param key  the key to search for next from
     * @return the next key, null if no match or at end
     */
    K nextKey(K key);

    /**
     * Gets the previous key before the one specified.
     *
     * @param key  the key to search for previous from
     * @return the previous key, null if no match or at start
     */
    K previousKey(K key);

}
