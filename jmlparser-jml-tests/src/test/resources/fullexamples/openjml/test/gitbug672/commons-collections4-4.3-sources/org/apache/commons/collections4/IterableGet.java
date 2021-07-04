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
 * The "read" subset of the {@link java.util.Map} interface.
 *
 * @param <K> the type of the keys in this map
 * @param <V> the type of the values in this map
 *
 * @since 4.0
 * @see Put
 */
public interface IterableGet<K, V> extends Get<K, V> {
    /**
     * Obtains a <code>MapIterator</code> over the map.
     * <p>
     * A map iterator is an efficient way of iterating over maps.
     * There is no need to access the entry set or use Map Entry objects.
     * <pre>
     * IterableMap&lt;String,Integer&gt; map = new HashedMap&lt;String,Integer&gt;();
     * MapIterator&lt;String,Integer&gt; it = map.mapIterator();
     * while (it.hasNext()) {
     *   String key = it.next();
     *   Integer value = it.getValue();
     *   it.setValue(value + 1);
     * }
     * </pre>
     *
     * @return a map iterator
     */
    MapIterator<K, V> mapIterator();

}
