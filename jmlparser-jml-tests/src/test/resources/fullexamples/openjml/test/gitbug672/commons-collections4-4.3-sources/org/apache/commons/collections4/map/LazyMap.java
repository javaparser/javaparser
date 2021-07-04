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

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.util.Map;

import org.apache.commons.collections4.Factory;
import org.apache.commons.collections4.Transformer;
import org.apache.commons.collections4.functors.FactoryTransformer;

/**
 * Decorates another <code>Map</code> to create objects in the map on demand.
 * <p>
 * When the {@link #get(Object)} method is called with a key that does not
 * exist in the map, the factory is used to create the object. The created
 * object will be added to the map using the requested key.
 * <p>
 * For instance:
 * <pre>
 * Factory&lt;Date&gt; factory = new Factory&lt;Date&gt;() {
 *     public Date create() {
 *         return new Date();
 *     }
 * }
 * Map&lt;String, Date&gt; lazy = LazyMap.lazyMap(new HashMap&lt;String, Date&gt;(), factory);
 * Date date = lazy.get("NOW");
 * </pre>
 *
 * After the above code is executed, <code>date</code> will refer to
 * a new <code>Date</code> instance. Furthermore, that <code>Date</code>
 * instance is mapped to the "NOW" key in the map.
 * <p>
 * <strong>Note that LazyMap is not synchronized and is not thread-safe.</strong>
 * If you wish to use this map from multiple threads concurrently, you must use
 * appropriate synchronization. The simplest approach is to wrap this map
 * using {@link java.util.Collections#synchronizedMap(Map)}. This class may throw
 * exceptions when accessed by concurrent threads without synchronization.
 * <p>
 * This class is Serializable from Commons Collections 3.1.
 *
 * @param <K> the type of the keys in this map
 * @param <V> the type of the values in this map
 * @since 3.0
 */
public class LazyMap<K, V> extends AbstractMapDecorator<K, V> implements Serializable {

    /** Serialization version */
    private static final long serialVersionUID = 7990956402564206740L;

    /** The factory to use to construct elements */
    protected final Transformer<? super K, ? extends V> factory;

    /**
     * Factory method to create a lazily instantiated map.
     *
     * @param <K>  the key type
     * @param <V>  the value type
     * @param map  the map to decorate, must not be null
     * @param factory  the factory to use, must not be null
     * @return a new lazy map
     * @throws NullPointerException if map or factory is null
     * @since 4.0
     */
    public static <K, V> LazyMap<K, V> lazyMap(final Map<K, V> map, final Factory< ? extends V> factory) {
        return new LazyMap<>(map, factory);
    }

    /**
     * Factory method to create a lazily instantiated map.
     *
     * @param <K>  the key type
     * @param <V>  the value type
     * @param map  the map to decorate, must not be null
     * @param factory  the factory to use, must not be null
     * @return a new lazy map
     * @throws NullPointerException if map or factory is null
     * @since 4.0
     */
    public static <V, K> LazyMap<K, V> lazyMap(final Map<K, V> map, final Transformer<? super K, ? extends V> factory) {
        return new LazyMap<>(map, factory);
    }

    //-----------------------------------------------------------------------
    /**
     * Constructor that wraps (not copies).
     *
     * @param map  the map to decorate, must not be null
     * @param factory  the factory to use, must not be null
     * @throws NullPointerException if map or factory is null
     */
    protected LazyMap(final Map<K,V> map, final Factory<? extends V> factory) {
        super(map);
        if (factory == null) {
            throw new NullPointerException("Factory must not be null");
        }
        this.factory = FactoryTransformer.factoryTransformer(factory);
    }

    /**
     * Constructor that wraps (not copies).
     *
     * @param map  the map to decorate, must not be null
     * @param factory  the factory to use, must not be null
     * @throws NullPointerException if map or factory is null
     */
    protected LazyMap(final Map<K,V> map, final Transformer<? super K, ? extends V> factory) {
        super(map);
        if (factory == null) {
            throw new NullPointerException("Factory must not be null");
        }
        this.factory = factory;
    }

    //-----------------------------------------------------------------------
    /**
     * Write the map out using a custom routine.
     *
     * @param out  the output stream
     * @throws IOException if an error occurs while writing to the stream
     * @since 3.1
     */
    private void writeObject(final ObjectOutputStream out) throws IOException {
        out.defaultWriteObject();
        out.writeObject(map);
    }

    /**
     * Read the map in using a custom routine.
     *
     * @param in  the input stream
     * @throws IOException if an error occurs while reading from the stream
     * @throws ClassNotFoundException if an object read from the stream can not be loaded
     * @since 3.1
     */
    @SuppressWarnings("unchecked")
    private void readObject(final ObjectInputStream in) throws IOException, ClassNotFoundException {
        in.defaultReadObject();
        map = (Map<K, V>) in.readObject();
    }

    //-----------------------------------------------------------------------
    @Override
    public V get(final Object key) {
        // create value for key if key is not currently in the map
        if (map.containsKey(key) == false) {
            @SuppressWarnings("unchecked")
            final K castKey = (K) key;
            final V value = factory.transform(castKey);
            map.put(castKey, value);
            return value;
        }
        return map.get(key);
    }

    // no need to wrap keySet, entrySet or values as they are views of
    // existing map entries - you can't do a map-style get on them.
}
