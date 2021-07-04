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

import java.util.Iterator;
import java.util.Map;

import org.apache.commons.collections4.CollectionUtils;
import org.apache.commons.collections4.FluentIterable;
import org.apache.commons.collections4.MultiValuedMap;
import org.apache.commons.collections4.Transformer;

/**
 * Decorates another <code>MultiValuedMap</code> to transform objects that are added.
 * <p>
 * This class affects the MultiValuedMap put methods. Thus objects must be
 * removed or searched for using their transformed form. For example, if the
 * transformation converts Strings to Integers, you must use the Integer form to
 * remove objects.
 * <p>
 * <strong>Note that TransformedMultiValuedMap is not synchronized and is not thread-safe.</strong>
 *
 * @param <K> the type of the keys in this map
 * @param <V> the type of the values in this map
 * @since 4.1
 */
public class TransformedMultiValuedMap<K, V> extends AbstractMultiValuedMapDecorator<K, V> {

    /** Serialization Version */
    private static final long serialVersionUID = 20150612L;

    /** The key transformer */
    private final Transformer<? super K, ? extends K> keyTransformer;

    /** The value transformer */
    private final Transformer<? super V, ? extends V> valueTransformer;

    /**
     * Factory method to create a transforming MultiValuedMap.
     * <p>
     * If there are any elements already in the map being decorated, they are
     * NOT transformed. Contrast this with
     * {@link #transformedMap(MultiValuedMap, Transformer, Transformer)}.
     *
     * @param <K> the key type
     * @param <V> the value type
     * @param map  the MultiValuedMap to decorate, may not be null
     * @param keyTransformer  the transformer to use for key conversion, null means no conversion
     * @param valueTransformer  the transformer to use for value conversion, null means no conversion
     * @return a new transformed MultiValuedMap
     * @throws NullPointerException if map is null
     */
    public static <K, V> TransformedMultiValuedMap<K, V> transformingMap(final MultiValuedMap<K, V> map,
            final Transformer<? super K, ? extends K> keyTransformer,
            final Transformer<? super V, ? extends V> valueTransformer) {
        return new TransformedMultiValuedMap<>(map, keyTransformer, valueTransformer);
    }

    /**
     * Factory method to create a transforming MultiValuedMap that will
     * transform existing contents of the specified map.
     * <p>
     * If there are any elements already in the map being decorated, they will
     * be transformed by this method. Contrast this with
     * {@link #transformingMap(MultiValuedMap, Transformer, Transformer)}.
     *
     * @param <K> the key type
     * @param <V> the value type
     * @param map  the MultiValuedMap to decorate, may not be null
     * @param keyTransformer  the transformer to use for key conversion, null means no conversion
     * @param valueTransformer  the transformer to use for value conversion, null means no conversion
     * @return a new transformed MultiValuedMap
     * @throws NullPointerException if map is null
     */
    public static <K, V> TransformedMultiValuedMap<K, V> transformedMap(final MultiValuedMap<K, V> map,
            final Transformer<? super K, ? extends K> keyTransformer,
            final Transformer<? super V, ? extends V> valueTransformer) {
        final TransformedMultiValuedMap<K, V> decorated =
                new TransformedMultiValuedMap<>(map, keyTransformer, valueTransformer);
        if (!map.isEmpty()) {
            final MultiValuedMap<K, V> mapCopy = new ArrayListValuedHashMap<>(map);
            decorated.clear();
            decorated.putAll(mapCopy);
        }
        return decorated;
    }

    // -----------------------------------------------------------------------
    /**
     * Constructor that wraps (not copies).
     * <p>
     * If there are any elements already in the collection being decorated, they
     * are NOT transformed.
     *
     * @param map  the MultiValuedMap to decorate, may not be null
     * @param keyTransformer  the transformer to use for key conversion, null means no conversion
     * @param valueTransformer  the transformer to use for value conversion, null means no conversion
     * @throws NullPointerException if map is null
     */
    protected TransformedMultiValuedMap(final MultiValuedMap<K, V> map,
            final Transformer<? super K, ? extends K> keyTransformer,
            final Transformer<? super V, ? extends V> valueTransformer) {
        super(map);
        this.keyTransformer = keyTransformer;
        this.valueTransformer = valueTransformer;
    }

    /**
     * Transforms a key.
     * <p>
     * The transformer itself may throw an exception if necessary.
     *
     * @param object  the object to transform
     * @return the transformed object
     */
    protected K transformKey(final K object) {
        if (keyTransformer == null) {
            return object;
        }
        return keyTransformer.transform(object);
    }

    /**
     * Transforms a value.
     * <p>
     * The transformer itself may throw an exception if necessary.
     *
     * @param object  the object to transform
     * @return the transformed object
     */
    protected V transformValue(final V object) {
        if (valueTransformer == null) {
            return object;
        }
        return valueTransformer.transform(object);
    }

    @Override
    public boolean put(final K key, final V value) {
        return decorated().put(transformKey(key), transformValue(value));
    }

    @Override
    public boolean putAll(final K key, final Iterable<? extends V> values) {
        if (values == null) {
            throw new NullPointerException("Values must not be null.");
        }

        final Iterable<V> transformedValues = FluentIterable.of(values).transform(valueTransformer);
        final Iterator<? extends V> it = transformedValues.iterator();
        return it.hasNext() && CollectionUtils.addAll(decorated().get(transformKey(key)), it);
    }

    @Override
    public boolean putAll(final Map<? extends K, ? extends V> map) {
        if (map == null) {
            throw new NullPointerException("Map must not be null.");
        }
        boolean changed = false;
        for (final Map.Entry<? extends K, ? extends V> entry : map.entrySet()) {
            changed |= put(entry.getKey(), entry.getValue());
        }
        return changed;
    }

    @Override
    public boolean putAll(final MultiValuedMap<? extends K, ? extends V> map) {
        if (map == null) {
            throw new NullPointerException("Map must not be null.");
        }
        boolean changed = false;
        for (final Map.Entry<? extends K, ? extends V> entry : map.entries()) {
            changed |= put(entry.getKey(), entry.getValue());
        }
        return changed;
    }

}
