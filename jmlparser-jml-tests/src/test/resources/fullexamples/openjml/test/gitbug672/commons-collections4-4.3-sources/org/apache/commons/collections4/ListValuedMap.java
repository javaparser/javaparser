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

import java.util.List;

/**
 * Defines a map that holds a list of values against each key.
 * <p>
 * A {@code ListValuedMap} is a Map with slightly different semantics:
 * <ul>
 *   <li>Putting a value into the map will add the value to a {@link List} at that key.</li>
 *   <li>Getting a value will return a {@link List}, holding all the values put to that key.</li>
 * </ul>
 *
 * @param <K> the type of the keys in this map
 * @param <V> the type of the values in this map
 * @since 4.1
 */
public interface ListValuedMap<K, V> extends MultiValuedMap<K, V> {

    /**
     * Gets the list of values associated with the specified key.
     * <p>
     * This method will return an <b>empty</b> list if
     * {@link #containsKey(Object)} returns {@code false}. Changes to the
     * returned list will update the underlying {@code ListValuedMap} and
     * vice-versa.
     *
     * @param key  the key to retrieve
     * @return the {@code List} of values, implementations should return an
     *   empty {@code List} for no mapping
     * @throws NullPointerException if the key is null and null keys are invalid
     */
    @Override
    List<V> get(K key);

    /**
     * Removes all values associated with the specified key.
     * <p>
     * The returned list <i>may</i> be modifiable, but updates will not be
     * propagated to this list-valued map. In case no mapping was stored for the
     * specified key, an empty, unmodifiable list will be returned.
     *
     * @param key  the key to remove values from
     * @return the {@code List} of values removed, implementations
     *   typically return an empty, unmodifiable {@code List} for no mapping found
     * @throws UnsupportedOperationException if the map is unmodifiable
     * @throws NullPointerException if the key is null and null keys are invalid
     */
    @Override
    List<V> remove(Object key);

}
