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
package org.apache.commons.collections4.bidimap;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.util.LinkedHashMap;
import java.util.Map;

import org.apache.commons.collections4.BidiMap;

/**
 * Implementation of <code>BidiMap</code> that uses two <code>LinkedHashMap</code> instances.
 * <p>
 * Two <code>LinkedHashMap</code> instances are used in this class.
 * This provides fast lookups at the expense of storing two sets of map entries and two linked lists.
 *
 * @param <K> the type of the keys in the map
 * @param <V> the type of the values in the map
 *
 * @since 4.0
 */
public class DualLinkedHashBidiMap<K, V> extends AbstractDualBidiMap<K, V> implements Serializable {

    /** Ensure serialization compatibility */
    private static final long serialVersionUID = 721969328361810L;

    /**
     * Creates an empty <code>HashBidiMap</code>.
     */
    public DualLinkedHashBidiMap() {
        super(new LinkedHashMap<K, V>(), new LinkedHashMap<V, K>());
    }

    /**
     * Constructs a <code>LinkedHashBidiMap</code> and copies the mappings from
     * specified <code>Map</code>.
     *
     * @param map the map whose mappings are to be placed in this map
     */
    public DualLinkedHashBidiMap(final Map<? extends K, ? extends V> map) {
        super(new LinkedHashMap<K, V>(), new LinkedHashMap<V, K>());
        putAll(map);
    }

    /**
     * Constructs a <code>LinkedHashBidiMap</code> that decorates the specified maps.
     *
     * @param normalMap      the normal direction map
     * @param reverseMap     the reverse direction map
     * @param inverseBidiMap the inverse BidiMap
     */
    protected DualLinkedHashBidiMap(final Map<K, V> normalMap, final Map<V, K> reverseMap,
                                    final BidiMap<V, K> inverseBidiMap) {
        super(normalMap, reverseMap, inverseBidiMap);
    }

    /**
     * Creates a new instance of this object.
     *
     * @param normalMap      the normal direction map
     * @param reverseMap     the reverse direction map
     * @param inverseBidiMap the inverse BidiMap
     * @return new bidi map
     */
    @Override
    protected BidiMap<V, K> createBidiMap(final Map<V, K> normalMap, final Map<K, V> reverseMap,
            final BidiMap<K, V> inverseBidiMap) {
        return new DualLinkedHashBidiMap<>(normalMap, reverseMap, inverseBidiMap);
    }

    // Serialization
    //-----------------------------------------------------------------------
    private void writeObject(final ObjectOutputStream out) throws IOException {
        out.defaultWriteObject();
        out.writeObject(normalMap);
    }

    private void readObject(final ObjectInputStream in) throws IOException, ClassNotFoundException {
        in.defaultReadObject();
        normalMap = new LinkedHashMap<>();
        reverseMap = new LinkedHashMap<>();
        @SuppressWarnings("unchecked") // will fail at runtime if stream is incorrect
        final Map<K, V> map = (Map<K, V>) in.readObject();
        putAll(map);
    }
}
