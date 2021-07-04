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
package org.apache.commons.collections4.set;

import java.io.Serializable;
import java.util.Collection;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

/**
 * Decorates a <code>Map</code> to obtain <code>Set</code> behaviour.
 * <p>
 * This class is used to create a <code>Set</code> with the same properties as
 * the key set of any map. Thus, a ReferenceSet can be created by wrapping a
 * <code>ReferenceMap</code> in an instance of this class.
 * <p>
 * Most map implementation can be used to create a set by passing in dummy values.
 * Exceptions include <code>BidiMap</code> implementations, as they require unique values.
 *
 * @param <E> the type of the elements in this set
 * @param <V> the dummy value type in this map
 * @since 3.1
 */
public final class MapBackedSet<E, V> implements Set<E>, Serializable {

    /** Serialization version */
    private static final long serialVersionUID = 6723912213766056587L;

    /** The map being used as the backing store */
    private final Map<E, ? super V> map;

    /** The dummyValue to use */
    private final V dummyValue;

    /**
     * Factory method to create a set from a map.
     *
     * @param <E> the element type
     * @param <V> the dummy value type in the map
     * @param map  the map to decorate, must not be null
     * @return a new map backed set
     * @throws NullPointerException if map is null
     * @since 4.0
     */
    public static <E, V> MapBackedSet<E, V> mapBackedSet(final Map<E, ? super V> map) {
        return mapBackedSet(map, null);
    }

    /**
     * Factory method to create a set from a map.
     *
     * @param <E> the element type
     * @param <V> the dummy value type in the map
     * @param map  the map to decorate, must not be null
     * @param dummyValue  the dummy value to use
     * @return a new map backed set
     * @throws NullPointerException if map is null
     * @since 4.0
     */
    public static <E, V> MapBackedSet<E, V> mapBackedSet(final Map<E, ? super V> map, final V dummyValue) {
        return new MapBackedSet<>(map, dummyValue);
    }

    //-----------------------------------------------------------------------
    /**
     * Constructor that wraps (not copies).
     *
     * @param map  the map to decorate, must not be null
     * @param dummyValue  the dummy value to use
     * @throws NullPointerException if map is null
     */
    private MapBackedSet(final Map<E, ? super V> map, final V dummyValue) {
        super();
        if (map == null) {
            throw new NullPointerException("The map must not be null");
        }
        this.map = map;
        this.dummyValue = dummyValue;
    }

    //-----------------------------------------------------------------------
    @Override
    public int size() {
        return map.size();
    }

    @Override
    public boolean isEmpty() {
        return map.isEmpty();
    }

    @Override
    public Iterator<E> iterator() {
        return map.keySet().iterator();
    }

    @Override
    public boolean contains(final Object obj) {
        return map.containsKey(obj);
    }

    @Override
    public boolean containsAll(final Collection<?> coll) {
        return map.keySet().containsAll(coll);
    }

    @Override
    public boolean add(final E obj) {
        final int size = map.size();
        map.put(obj, dummyValue);
        return map.size() != size;
    }

    @Override
    public boolean addAll(final Collection<? extends E> coll) {
        final int size = map.size();
        for (final E e : coll) {
            map.put(e, dummyValue);
        }
        return map.size() != size;
    }

    @Override
    public boolean remove(final Object obj) {
        final int size = map.size();
        map.remove(obj);
        return map.size() != size;
    }

    @Override
    public boolean removeAll(final Collection<?> coll) {
        return map.keySet().removeAll(coll);
    }

    @Override
    public boolean retainAll(final Collection<?> coll) {
        return map.keySet().retainAll(coll);
    }

    @Override
    public void clear() {
        map.clear();
    }

    @Override
    public Object[] toArray() {
        return map.keySet().toArray();
    }

    @Override
    public <T> T[] toArray(final T[] array) {
        return map.keySet().toArray(array);
    }

    @Override
    public boolean equals(final Object obj) {
        return map.keySet().equals(obj);
    }

    @Override
    public int hashCode() {
        return map.keySet().hashCode();
    }

}
