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
package org.apache.commons.collections4.splitmap;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.util.Map;

import org.apache.commons.collections4.Put;
import org.apache.commons.collections4.Transformer;
import org.apache.commons.collections4.map.LinkedMap;

/**
 * Decorates another {@link Map} to transform objects that are added.
 * <p>
 * The Map put methods and Map.Entry setValue method are affected by this class.
 * Thus objects must be removed or searched for using their transformed form.
 * For example, if the transformation converts Strings to Integers, you must use
 * the Integer form to remove objects.
 * <p>
 * <strong>Note that TransformedMap is not synchronized and is not
 * thread-safe.</strong> If you wish to use this map from multiple threads
 * concurrently, you must use appropriate synchronization. The simplest approach
 * is to wrap this map using {@link java.util.Collections#synchronizedMap(Map)}.
 * This class may throw exceptions when accessed by concurrent threads without
 * synchronization.
 * <p>
 * The "put" and "get" type constraints of this class are mutually independent;
 * contrast with {@link org.apache.commons.collections4.map.TransformedMap} which,
 * by virtue of its implementing {@link Map}&lt;K, V&gt;, must be constructed in such
 * a way that its read and write parameters are generalized to a common (super-)type.
 * In practice this would often mean <code>&gt;Object, Object&gt;</code>, defeating
 * much of the usefulness of having parameterized types.
 * <p>
 * On the downside, this class is not drop-in compatible with {@link java.util.Map}
 * but is intended to be worked with either directly or by {@link Put} and
 * {@link org.apache.commons.collections4.Get Get} generalizations.
 *
 * @param <J> the type of the keys to put in this map
 * @param <K> the type of the keys to get in this map
 * @param <U> the type of the values to put in this map
 * @param <V> the type of the values to get in this map
 * @since 4.0
 *
 * @see org.apache.commons.collections4.SplitMapUtils#readableMap(org.apache.commons.collections4.Get)
 * @see org.apache.commons.collections4.SplitMapUtils#writableMap(Put)
 */
public class TransformedSplitMap<J, K, U, V> extends AbstractIterableGetMapDecorator<K, V>
        implements Put<J, U>, Serializable {

    /** Serialization version */
    private static final long serialVersionUID = 5966875321133456994L;

    /** The transformer to use for the key */
    private final Transformer<? super J, ? extends K> keyTransformer;
    /** The transformer to use for the value */
    private final Transformer<? super U, ? extends V> valueTransformer;

    /**
     * Factory method to create a transforming map.
     * <p>
     * If there are any elements already in the map being decorated, they are
     * NOT transformed.
     *
     * @param <J>  the input key type
     * @param <K>  the output key type
     * @param <U>  the input value type
     * @param <V>  the output value type
     * @param map the map to decorate, must not be null
     * @param keyTransformer the transformer to use for key conversion, must not be null
     * @param valueTransformer the transformer to use for value conversion, must not be null
     * @return a new transformed map
     * @throws NullPointerException if map or either of the transformers is null
     */
    public static <J, K, U, V> TransformedSplitMap<J, K, U, V> transformingMap(final Map<K, V> map,
            final Transformer<? super J, ? extends K> keyTransformer,
            final Transformer<? super U, ? extends V> valueTransformer) {
        return new TransformedSplitMap<>(map, keyTransformer, valueTransformer);
    }

    //-----------------------------------------------------------------------
    /**
     * Constructor that wraps (not copies).
     * <p>
     * If there are any elements already in the collection being decorated, they
     * are NOT transformed.
     *
     * @param map the map to decorate, must not be null
     * @param keyTransformer the transformer to use for key conversion, must not be null
     * @param valueTransformer the transformer to use for value conversion, must not be null
     * @throws NullPointerException if map or either of the transformers is null
     */
    protected TransformedSplitMap(final Map<K, V> map, final Transformer<? super J, ? extends K> keyTransformer,
            final Transformer<? super U, ? extends V> valueTransformer) {
        super(map);
        if (keyTransformer == null) {
            throw new NullPointerException("KeyTransformer must not be null.");
        }
        this.keyTransformer = keyTransformer;
        if (valueTransformer == null) {
            throw new NullPointerException("ValueTransformer must not be null.");
        }
        this.valueTransformer = valueTransformer;
    }

    //-----------------------------------------------------------------------
    /**
     * Write the map out using a custom routine.
     *
     * @param out the output stream
     * @throws IOException if an error occurs while writing to the stream
     */
    private void writeObject(final ObjectOutputStream out) throws IOException {
        out.defaultWriteObject();
        out.writeObject(decorated());
    }

    /**
     * Read the map in using a custom routine.
     *
     * @param in the input stream
     * @throws IOException if an error occurs while reading from the stream
     * @throws ClassNotFoundException if an object read from the stream can not be loaded
     * @since 3.1
     */
    @SuppressWarnings("unchecked") // (1) should only fail if input stream is incorrect
    private void readObject(final ObjectInputStream in) throws IOException, ClassNotFoundException {
        in.defaultReadObject();
        map = (Map<K, V>) in.readObject(); // (1)
    }

    //-----------------------------------------------------------------------
    /**
     * Transforms a key.
     * <p>
     * The transformer itself may throw an exception if necessary.
     *
     * @param object the object to transform
     * @return the transformed object
     */
    protected K transformKey(final J object) {
        return keyTransformer.transform(object);
    }

    /**
     * Transforms a value.
     * <p>
     * The transformer itself may throw an exception if necessary.
     *
     * @param object the object to transform
     * @return the transformed object
     */
    protected V transformValue(final U object) {
        return valueTransformer.transform(object);
    }

    /**
     * Transforms a map.
     * <p>
     * The transformer itself may throw an exception if necessary.
     *
     * @param map the map to transform
     * @return the transformed object
     */
    @SuppressWarnings("unchecked")
    protected Map<K, V> transformMap(final Map<? extends J, ? extends U> map) {
        if (map.isEmpty()) {
            return (Map<K, V>) map;
        }
        final Map<K, V> result = new LinkedMap<>(map.size());

        for (final Map.Entry<? extends J, ? extends U> entry : map.entrySet()) {
            result.put(transformKey(entry.getKey()), transformValue(entry.getValue()));
        }
        return result;
    }

    /**
     * Override to transform the value when using <code>setValue</code>.
     *
     * @param value the value to transform
     * @return the transformed value
     */
    protected V checkSetValue(final U value) {
        return valueTransformer.transform(value);
    }

    //-----------------------------------------------------------------------
    @Override
    public V put(final J key, final U value) {
        return decorated().put(transformKey(key), transformValue(value));
    }

    @Override
    public void putAll(final Map<? extends J, ? extends U> mapToCopy) {
        decorated().putAll(transformMap(mapToCopy));
    }

    @Override
    public void clear() {
        decorated().clear();
    }
}
