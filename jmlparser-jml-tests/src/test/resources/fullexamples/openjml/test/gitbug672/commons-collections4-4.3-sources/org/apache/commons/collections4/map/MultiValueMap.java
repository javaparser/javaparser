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
import java.util.AbstractCollection;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import org.apache.commons.collections4.CollectionUtils;
import org.apache.commons.collections4.Factory;
import org.apache.commons.collections4.FunctorException;
import org.apache.commons.collections4.MultiMap;
import org.apache.commons.collections4.Transformer;
import org.apache.commons.collections4.iterators.EmptyIterator;
import org.apache.commons.collections4.iterators.IteratorChain;
import org.apache.commons.collections4.iterators.LazyIteratorChain;
import org.apache.commons.collections4.iterators.TransformIterator;

/**
 * A MultiValueMap decorates another map, allowing it to have
 * more than one value for a key.
 * <p>
 * A <code>MultiMap</code> is a Map with slightly different semantics.
 * Putting a value into the map will add the value to a Collection at that key.
 * Getting a value will return a Collection, holding all the values put to that key.
 * <p>
 * This implementation is a decorator, allowing any Map implementation
 * to be used as the base.
 * <p>
 * In addition, this implementation allows the type of collection used
 * for the values to be controlled. By default, an <code>ArrayList</code>
 * is used, however a <code>Class</code> to instantiate may be specified,
 * or a factory that returns a <code>Collection</code> instance.
 * <p>
 * <strong>Note that MultiValueMap is not synchronized and is not thread-safe.</strong>
 * If you wish to use this map from multiple threads concurrently, you must use
 * appropriate synchronization. This class may throw exceptions when accessed
 * by concurrent threads without synchronization.
 *
 * @param <K> the type of the keys in this map
 * @param <V> the type of the values in this map
 * @since 3.2
 * @deprecated since 4.1, use {@link org.apache.commons.collections4.MultiValuedMap MultiValuedMap} instead
 */
@Deprecated
public class MultiValueMap<K, V> extends AbstractMapDecorator<K, Object> implements MultiMap<K, V>, Serializable {

    /** Serialization version */
    private static final long serialVersionUID = -2214159910087182007L;

    /** The factory for creating value collections. */
    private final Factory<? extends Collection<V>> collectionFactory;
    /** The cached values. */
    private transient Collection<V> valuesView;

    /**
     * Creates a map which wraps the given map and
     * maps keys to ArrayLists.
     *
     * @param <K>  the key type
     * @param <V>  the value type
     * @param map  the map to wrap
     * @return a new multi-value map
     * @since 4.0
     */
    @SuppressWarnings({ "unchecked", "rawtypes" })
    public static <K, V> MultiValueMap<K, V> multiValueMap(final Map<K, ? super Collection<V>> map) {
        return MultiValueMap.<K, V, ArrayList> multiValueMap((Map<K, ? super Collection>) map, ArrayList.class);
    }

    /**
     * Creates a map which decorates the given <code>map</code> and
     * maps keys to collections of type <code>collectionClass</code>.
     *
     * @param <K>  the key type
     * @param <V>  the value type
     * @param <C>  the collection class type
     * @param map  the map to wrap
     * @param collectionClass  the type of the collection class
     * @return a new multi-value map
     * @since 4.0
     */
    public static <K, V, C extends Collection<V>> MultiValueMap<K, V> multiValueMap(final Map<K, ? super C> map,
                                                                                    final Class<C> collectionClass) {
        return new MultiValueMap<>(map, new ReflectionFactory<>(collectionClass));
    }

    /**
     * Creates a map which decorates the given <code>map</code> and
     * creates the value collections using the supplied <code>collectionFactory</code>.
     *
     * @param <K>  the key type
     * @param <V>  the value type
     * @param <C>  the collection class type
     * @param map  the map to decorate
     * @param collectionFactory  the collection factory (must return a Collection object).
     * @return a new multi-value map
     * @since 4.0
     */
    public static <K, V, C extends Collection<V>> MultiValueMap<K, V> multiValueMap(final Map<K, ? super C> map,
            final Factory<C> collectionFactory) {
        return new MultiValueMap<>(map, collectionFactory);
    }

    //-----------------------------------------------------------------------
    /**
     * Creates a MultiValueMap based on a <code>HashMap</code> and
     * storing the multiple values in an <code>ArrayList</code>.
     */
    @SuppressWarnings({ "unchecked", "rawtypes" })
    public MultiValueMap() {
        this(new HashMap<K, V>(), new ReflectionFactory(ArrayList.class));
    }

    /**
     * Creates a MultiValueMap which decorates the given <code>map</code> and
     * creates the value collections using the supplied <code>collectionFactory</code>.
     *
     * @param <C>  the collection class type
     * @param map  the map to decorate
     * @param collectionFactory  the collection factory which must return a Collection instance
     */
    @SuppressWarnings("unchecked")
    protected <C extends Collection<V>> MultiValueMap(final Map<K, ? super C> map,
                                                      final Factory<C> collectionFactory) {
        super((Map<K, Object>) map);
        if (collectionFactory == null) {
            throw new IllegalArgumentException("The factory must not be null");
        }
        this.collectionFactory = collectionFactory;
    }

    //-----------------------------------------------------------------------
    /**
     * Write the map out using a custom routine.
     *
     * @param out  the output stream
     * @throws IOException if an error occurs while writing to the stream
     * @since 4.0
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
     * @since 4.0
     */
    @SuppressWarnings("unchecked") // (1) should only fail if input stream is incorrect
    private void readObject(final ObjectInputStream in) throws IOException, ClassNotFoundException {
        in.defaultReadObject();
        map = (Map<K, Object>) in.readObject(); // (1)
    }

    //-----------------------------------------------------------------------
    /**
     * Clear the map.
     */
    @Override
    public void clear() {
        // If you believe that you have GC issues here, try uncommenting this code
//        Set pairs = getMap().entrySet();
//        Iterator pairsIterator = pairs.iterator();
//        while (pairsIterator.hasNext()) {
//            Map.Entry keyValuePair = (Map.Entry) pairsIterator.next();
//            Collection coll = (Collection) keyValuePair.getValue();
//            coll.clear();
//        }
        decorated().clear();
    }

    /**
     * Removes a specific value from map.
     * <p>
     * The item is removed from the collection mapped to the specified key.
     * Other values attached to that key are unaffected.
     * <p>
     * If the last value for a key is removed, <code>null</code> will be returned
     * from a subsequent <code>get(key)</code>.
     *
     * @param key  the key to remove from
     * @param value the value to remove
     * @return {@code true} if the mapping was removed, {@code false} otherwise
     */
    @Override
    public boolean removeMapping(final Object key, final Object value) {
        final Collection<V> valuesForKey = getCollection(key);
        if (valuesForKey == null) {
            return false;
        }
        final boolean removed = valuesForKey.remove(value);
        if (removed == false) {
            return false;
        }
        if (valuesForKey.isEmpty()) {
            remove(key);
        }
        return true;
    }

    /**
     * Checks whether the map contains the value specified.
     * <p>
     * This checks all collections against all keys for the value, and thus could be slow.
     *
     * @param value  the value to search for
     * @return true if the map contains the value
     */
    @Override
    @SuppressWarnings("unchecked")
    public boolean containsValue(final Object value) {
        final Set<Map.Entry<K, Object>> pairs = decorated().entrySet();
        if (pairs != null) {
            for (final Map.Entry<K, Object> entry : pairs) {
                if (((Collection<V>) entry.getValue()).contains(value)) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * Adds the value to the collection associated with the specified key.
     * <p>
     * Unlike a normal <code>Map</code> the previous value is not replaced.
     * Instead the new value is added to the collection stored against the key.
     *
     * @param key  the key to store against
     * @param value  the value to add to the collection at the key
     * @return the value added if the map changed and null if the map did not change
     */
    @Override
    @SuppressWarnings("unchecked")
    public Object put(final K key, final Object value) {
        boolean result = false;
        Collection<V> coll = getCollection(key);
        if (coll == null) {
            coll = createCollection(1);  // might produce a non-empty collection
            coll.add((V) value);
            if (coll.size() > 0) {
                // only add if non-zero size to maintain class state
                decorated().put(key, coll);
                result = true;  // map definitely changed
            }
        } else {
            result = coll.add((V) value);
        }
        return result ? value : null;
    }

    /**
     * Override superclass to ensure that MultiMap instances are
     * correctly handled.
     * <p>
     * If you call this method with a normal map, each entry is
     * added using <code>put(Object,Object)</code>.
     * If you call this method with a multi map, each entry is
     * added using <code>putAll(Object,Collection)</code>.
     *
     * @param map  the map to copy (either a normal or multi map)
     */
    @Override
    @SuppressWarnings("unchecked")
    public void putAll(final Map<? extends K, ?> map) {
        if (map instanceof MultiMap) {
            for (final Map.Entry<? extends K, Object> entry : ((MultiMap<? extends K, V>) map).entrySet()) {
                putAll(entry.getKey(), (Collection<V>) entry.getValue());
            }
        } else {
            for (final Map.Entry<? extends K, ?> entry : map.entrySet()) {
                put(entry.getKey(), entry.getValue());
            }
        }
    }

    /**
     * {@inheritDoc}
     * <p>
     * NOTE: the returned Entry objects will contain as value a {@link Collection}
     * of all values that are mapped to the given key. To get a "flattened" version
     * of all mappings contained in this map, use {@link #iterator()}.
     *
     * @see #iterator()
     */
    @Override
    public Set<Entry<K, Object>> entrySet() { // NOPMD
        return super.entrySet();
    }

    /**
     * Gets a collection containing all the values in the map.
     * <p>
     * This returns a collection containing the combination of values from all keys.
     *
     * @return a collection view of the values contained in this map
     */
    @Override
    @SuppressWarnings("unchecked")
    public Collection<Object> values() {
        final Collection<V> vs = valuesView;
        return (Collection<Object>) (vs != null ? vs : (valuesView = new Values()));
    }

    /**
     * Checks whether the collection at the specified key contains the value.
     *
     * @param key  the key to search for
     * @param value  the value to search for
     * @return true if the map contains the value
     */
    public boolean containsValue(final Object key, final Object value) {
        final Collection<V> coll = getCollection(key);
        if (coll == null) {
            return false;
        }
        return coll.contains(value);
    }

    /**
     * Gets the collection mapped to the specified key.
     * This method is a convenience method to typecast the result of <code>get(key)</code>.
     *
     * @param key  the key to retrieve
     * @return the collection mapped to the key, null if no mapping
     */
    @SuppressWarnings("unchecked")
    public Collection<V> getCollection(final Object key) {
        return (Collection<V>) decorated().get(key);
    }

    /**
     * Gets the size of the collection mapped to the specified key.
     *
     * @param key  the key to get size for
     * @return the size of the collection at the key, zero if key not in map
     */
    public int size(final Object key) {
        final Collection<V> coll = getCollection(key);
        if (coll == null) {
            return 0;
        }
        return coll.size();
    }

    /**
     * Adds a collection of values to the collection associated with
     * the specified key.
     *
     * @param key  the key to store against
     * @param values  the values to add to the collection at the key, null ignored
     * @return true if this map changed
     */
    public boolean putAll(final K key, final Collection<V> values) {
        if (values == null || values.size() == 0) {
            return false;
        }
        boolean result = false;
        Collection<V> coll = getCollection(key);
        if (coll == null) {
            coll = createCollection(values.size());  // might produce a non-empty collection
            coll.addAll(values);
            if (coll.size() > 0) {
                // only add if non-zero size to maintain class state
                decorated().put(key, coll);
                result = true;  // map definitely changed
            }
        } else {
            result = coll.addAll(values);
        }
        return result;
    }

    /**
     * Gets an iterator for the collection mapped to the specified key.
     *
     * @param key  the key to get an iterator for
     * @return the iterator of the collection at the key, empty iterator if key not in map
     */
    public Iterator<V> iterator(final Object key) {
        if (!containsKey(key)) {
            return EmptyIterator.<V>emptyIterator();
        }
        return new ValuesIterator(key);
    }

    /**
     * Gets an iterator for all mappings stored in this {@link MultiValueMap}.
     * <p>
     * The iterator will return multiple Entry objects with the same key
     * if there are multiple values mapped to this key.
     * <p>
     * NOTE: calling {@link java.util.Map.Entry#setValue(Object)} on any of the returned
     * elements will result in a {@link UnsupportedOperationException}.
     *
     * @return the iterator of all mappings in this map
     * @since 4.0
     */
    public Iterator<Entry<K, V>> iterator() {
        final Collection<K> allKeys = new ArrayList<>(keySet());
        final Iterator<K> keyIterator = allKeys.iterator();

        return new LazyIteratorChain<Entry<K, V>>() {
            @Override
            protected Iterator<? extends Entry<K, V>> nextIterator(final int count) {
                if ( ! keyIterator.hasNext() ) {
                    return null;
                }
                final K key = keyIterator.next();
                final Transformer<V, Entry<K, V>> transformer = new Transformer<V, Entry<K, V>>() {
                    @Override
                    public Entry<K, V> transform(final V input) {
                        return new Entry<K, V>() {
                            @Override
                            public K getKey() {
                                return key;
                            }
                            @Override
                            public V getValue() {
                                return input;
                            }
                            @Override
                            public V setValue(final V value) {
                                throw new UnsupportedOperationException();
                            }
                        };
                    }
                };
                return new TransformIterator<>(new ValuesIterator(key), transformer);
            }
        };
    }

    /**
     * Gets the total size of the map by counting all the values.
     *
     * @return the total size of the map counting all values
     */
    public int totalSize() {
        int total = 0;
        for (final Object v : decorated().values()) {
            total += CollectionUtils.size(v);
        }
        return total;
    }

    /**
     * Creates a new instance of the map value Collection container
     * using the factory.
     * <p>
     * This method can be overridden to perform your own processing
     * instead of using the factory.
     *
     * @param size  the collection size that is about to be added
     * @return the new collection
     */
    protected Collection<V> createCollection(final int size) {
        return collectionFactory.create();
    }

    //-----------------------------------------------------------------------
    /**
     * Inner class that provides the values view.
     */
    private class Values extends AbstractCollection<V> {
        @Override
        public Iterator<V> iterator() {
            final IteratorChain<V> chain = new IteratorChain<>();
            for (final K k : keySet()) {
                chain.addIterator(new ValuesIterator(k));
            }
            return chain;
        }

        @Override
        public int size() {
            return totalSize();
        }

        @Override
        public void clear() {
            MultiValueMap.this.clear();
        }
    }

    /**
     * Inner class that provides the values iterator.
     */
    private class ValuesIterator implements Iterator<V> {
        private final Object key;
        private final Collection<V> values;
        private final Iterator<V> iterator;

        public ValuesIterator(final Object key) {
            this.key = key;
            this.values = getCollection(key);
            this.iterator = values.iterator();
        }

        @Override
        public void remove() {
            iterator.remove();
            if (values.isEmpty()) {
                MultiValueMap.this.remove(key);
            }
        }

        @Override
        public boolean hasNext() {
            return iterator.hasNext();
        }

        @Override
        public V next() {
            return iterator.next();
        }
    }

    /**
     * Inner class that provides a simple reflection factory.
     */
    private static class ReflectionFactory<T extends Collection<?>> implements Factory<T>, Serializable {

        /** Serialization version */
        private static final long serialVersionUID = 2986114157496788874L;

        private final Class<T> clazz;

        public ReflectionFactory(final Class<T> clazz) {
            this.clazz = clazz;
        }

        @Override
        public T create() {
            try {
                return clazz.getDeclaredConstructor().newInstance();
            } catch (final Exception ex) {
                throw new FunctorException("Cannot instantiate class: " + clazz, ex);
            }
        }

        private void readObject(final ObjectInputStream is) throws IOException, ClassNotFoundException {
            is.defaultReadObject();
            // ensure that the de-serialized class is a Collection, COLLECTIONS-580
            if (clazz != null && !Collection.class.isAssignableFrom(clazz)) {
                throw new UnsupportedOperationException();
            }
        }
    }

}
