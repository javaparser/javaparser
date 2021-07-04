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

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.util.AbstractCollection;
import java.util.AbstractMap;
import java.util.AbstractSet;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.apache.commons.collections4.CollectionUtils;
import org.apache.commons.collections4.IteratorUtils;
import org.apache.commons.collections4.MapIterator;
import org.apache.commons.collections4.MultiSet;
import org.apache.commons.collections4.MultiValuedMap;
import org.apache.commons.collections4.Transformer;
import org.apache.commons.collections4.iterators.AbstractIteratorDecorator;
import org.apache.commons.collections4.iterators.EmptyMapIterator;
import org.apache.commons.collections4.iterators.IteratorChain;
import org.apache.commons.collections4.iterators.LazyIteratorChain;
import org.apache.commons.collections4.iterators.TransformIterator;
import org.apache.commons.collections4.keyvalue.AbstractMapEntry;
import org.apache.commons.collections4.keyvalue.UnmodifiableMapEntry;
import org.apache.commons.collections4.multiset.AbstractMultiSet;
import org.apache.commons.collections4.multiset.UnmodifiableMultiSet;

/**
 * Abstract implementation of the {@link MultiValuedMap} interface to simplify
 * the creation of subclass implementations.
 * <p>
 * Subclasses specify a Map implementation to use as the internal storage.
 *
 * @param <K> the type of the keys in this map
 * @param <V> the type of the values in this map
 * @since 4.1
 */
public abstract class AbstractMultiValuedMap<K, V> implements MultiValuedMap<K, V> {

    /** The values view */
    private transient Collection<V> valuesView;

    /** The EntryValues view */
    private transient EntryValues entryValuesView;

    /** The KeyMultiSet view */
    private transient MultiSet<K> keysMultiSetView;

    /** The AsMap view */
    private transient AsMap asMapView;

    /** The map used to store the data */
    private transient Map<K, Collection<V>> map;

    /**
     * Constructor needed for subclass serialisation.
     */
    protected AbstractMultiValuedMap() {
        super();
    }

    /**
     * Constructor that wraps (not copies).
     *
     * @param map  the map to wrap, must not be null
     * @throws NullPointerException if the map is null
     */
    @SuppressWarnings("unchecked")
    protected AbstractMultiValuedMap(final Map<K, ? extends Collection<V>> map) {
        if (map == null) {
            throw new NullPointerException("Map must not be null.");
        }
        this.map = (Map<K, Collection<V>>) map;
    }

    // -----------------------------------------------------------------------
    /**
     * Gets the map being wrapped.
     *
     * @return the wrapped map
     */
    protected Map<K, ? extends Collection<V>> getMap() {
        return map;
    }

    /**
     * Sets the map being wrapped.
     * <p>
     * <b>NOTE:</b> this method should only be used during deserialization
     *
     * @param map the map to wrap
     */
    @SuppressWarnings("unchecked")
    protected void setMap(final Map<K, ? extends Collection<V>> map) {
        this.map = (Map<K, Collection<V>>) map;
    }

    protected abstract Collection<V> createCollection();

    // -----------------------------------------------------------------------
    @Override
    public boolean containsKey(final Object key) {
        return getMap().containsKey(key);
    }

    @Override
    public boolean containsValue(final Object value) {
        return values().contains(value);
    }

    @Override
    public boolean containsMapping(final Object key, final Object value) {
        final Collection<V> coll = getMap().get(key);
        return coll != null && coll.contains(value);
    }

    @Override
    public Collection<Entry<K, V>> entries() {
        return entryValuesView != null ? entryValuesView : (entryValuesView = new EntryValues());
    }

    /**
     * Gets the collection of values associated with the specified key. This
     * would return an empty collection in case the mapping is not present
     *
     * @param key the key to retrieve
     * @return the {@code Collection} of values, will return an empty {@code Collection} for no mapping
     */
    @Override
    public Collection<V> get(final K key) {
        return wrappedCollection(key);
    }

    Collection<V> wrappedCollection(final K key) {
        return new WrappedCollection(key);
    }

    /**
     * Removes all values associated with the specified key.
     * <p>
     * A subsequent <code>get(Object)</code> would return an empty collection.
     *
     * @param key  the key to remove values from
     * @return the <code>Collection</code> of values removed, will return an
     *   empty, unmodifiable collection for no mapping found
     */
    @Override
    public Collection<V> remove(final Object key) {
        return CollectionUtils.emptyIfNull(getMap().remove(key));
    }

    /**
     * Removes a specific key/value mapping from the multi-valued map.
     * <p>
     * The value is removed from the collection mapped to the specified key.
     * Other values attached to that key are unaffected.
     * <p>
     * If the last value for a key is removed, an empty collection would be
     * returned from a subsequent {@link #get(Object)}.
     *
     * @param key the key to remove from
     * @param value the value to remove
     * @return true if the mapping was removed, false otherwise
     */
    @Override
    public boolean removeMapping(final Object key, final Object value) {
        final Collection<V> coll = getMap().get(key);
        if (coll == null) {
            return false;
        }
        final boolean changed = coll.remove(value);
        if (coll.isEmpty()) {
            getMap().remove(key);
        }
        return changed;
    }

    @Override
    public boolean isEmpty() {
        return getMap().isEmpty();
    }

    @Override
    public Set<K> keySet() {
        return getMap().keySet();
    }

    /**
     * {@inheritDoc}
     * <p>
     * This implementation does <b>not</b> cache the total size
     * of the multi-valued map, but rather calculates it by iterating
     * over the entries of the underlying map.
     */
    @Override
    public int size() {
        // the total size should be cached to improve performance
        // but this requires that all modifications of the multimap
        // (including the wrapped collections and entry/value
        // collections) are tracked.
        int size = 0;
        for (final Collection<V> col : getMap().values()) {
            size += col.size();
        }
        return size;
    }

    /**
     * Gets a collection containing all the values in the map.
     * <p>
     * Returns a collection containing all the values from all keys.
     *
     * @return a collection view of the values contained in this map
     */
    @Override
    public Collection<V> values() {
        final Collection<V> vs = valuesView;
        return vs != null ? vs : (valuesView = new Values());
    }

    @Override
    public void clear() {
        getMap().clear();
    }

    /**
     * Adds the value to the collection associated with the specified key.
     * <p>
     * Unlike a normal <code>Map</code> the previous value is not replaced.
     * Instead the new value is added to the collection stored against the key.
     *
     * @param key the key to store against
     * @param value the value to add to the collection at the key
     * @return the value added if the map changed and null if the map did not change
     */
    @Override
    public boolean put(final K key, final V value) {
        Collection<V> coll = getMap().get(key);
        if (coll == null) {
            coll = createCollection();
            if (coll.add(value)) {
                map.put(key, coll);
                return true;
            }
            return false;
        }
        return coll.add(value);
    }

    /**
     * Copies all of the mappings from the specified map to this map. The effect
     * of this call is equivalent to that of calling {@link #put(Object,Object)
     * put(k, v)} on this map once for each mapping from key {@code k} to value
     * {@code v} in the specified map. The behavior of this operation is
     * undefined if the specified map is modified while the operation is in
     * progress.
     *
     * @param map mappings to be stored in this map, may not be null
     * @return true if the map changed as a result of this operation
     * @throws NullPointerException if map is null
     */
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

    /**
     * Copies all of the mappings from the specified MultiValuedMap to this map.
     * The effect of this call is equivalent to that of calling
     * {@link #put(Object,Object) put(k, v)} on this map once for each mapping
     * from key {@code k} to value {@code v} in the specified map. The
     * behavior of this operation is undefined if the specified map is modified
     * while the operation is in progress.
     *
     * @param map mappings to be stored in this map, may not be null
     * @return true if the map changed as a result of this operation
     * @throws NullPointerException if map is null
     */
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

    /**
     * Returns a {@link MultiSet} view of the key mapping contained in this map.
     * <p>
     * Returns a MultiSet of keys with its values count as the count of the MultiSet.
     * This multiset is backed by the map, so any changes in the map is reflected here.
     * Any method which modifies this multiset like {@code add}, {@code remove},
     * {@link Iterator#remove()} etc throws {@code UnsupportedOperationException}.
     *
     * @return a bag view of the key mapping contained in this map
     */
    @Override
    public MultiSet<K> keys() {
        if (keysMultiSetView == null) {
            keysMultiSetView = UnmodifiableMultiSet.unmodifiableMultiSet(new KeysMultiSet());
        }
        return keysMultiSetView;
    }

    @Override
    public Map<K, Collection<V>> asMap() {
        return asMapView != null ? asMapView : (asMapView = new AsMap(map));
    }

    /**
     * Adds Iterable values to the collection associated with the specified key.
     *
     * @param key the key to store against
     * @param values the values to add to the collection at the key, may not be null
     * @return true if this map changed
     * @throws NullPointerException if values is null
     */
    @Override
    public boolean putAll(final K key, final Iterable<? extends V> values) {
        if (values == null) {
            throw new NullPointerException("Values must not be null.");
        }

        if (values instanceof Collection<?>) {
            final Collection<? extends V> valueCollection = (Collection<? extends V>) values;
            return !valueCollection.isEmpty() && get(key).addAll(valueCollection);
        }
        final Iterator<? extends V> it = values.iterator();
        return it.hasNext() && CollectionUtils.addAll(get(key), it);
    }

    @Override
    public MapIterator<K, V> mapIterator() {
        if (size() == 0) {
            return EmptyMapIterator.emptyMapIterator();
        }
        return new MultiValuedMapIterator();
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj instanceof MultiValuedMap) {
            return asMap().equals(((MultiValuedMap<?, ?>) obj).asMap());
        }
        return false;
    }

    @Override
    public int hashCode() {
        return getMap().hashCode();
    }

    @Override
    public String toString() {
        return getMap().toString();
    }

    // -----------------------------------------------------------------------

    /**
     * Wrapped collection to handle add and remove on the collection returned
     * by get(object).
     * <p>
     * Currently, the wrapped collection is not cached and has to be retrieved
     * from the underlying map. This is safe, but not very efficient and
     * should be improved in subsequent releases. For this purpose, the
     * scope of this collection is set to package private to simplify later
     * refactoring.
     */
    class WrappedCollection implements Collection<V> {

        protected final K key;

        public WrappedCollection(final K key) {
            this.key = key;
        }

        protected Collection<V> getMapping() {
            return getMap().get(key);
        }

        @Override
        public boolean add(final V value) {
            Collection<V> coll = getMapping();
            if (coll == null) {
                coll = createCollection();
                AbstractMultiValuedMap.this.map.put(key, coll);
            }
            return coll.add(value);
        }

        @Override
        public boolean addAll(final Collection<? extends V> other) {
            Collection<V> coll = getMapping();
            if (coll == null) {
                coll = createCollection();
                AbstractMultiValuedMap.this.map.put(key, coll);
            }
            return coll.addAll(other);
        }

        @Override
        public void clear() {
            final Collection<V> coll = getMapping();
            if (coll != null) {
                coll.clear();
                AbstractMultiValuedMap.this.remove(key);
            }
        }

        @Override
        @SuppressWarnings("unchecked")
        public Iterator<V> iterator() {
            final Collection<V> coll = getMapping();
            if (coll == null) {
                return IteratorUtils.EMPTY_ITERATOR;
            }
            return new ValuesIterator(key);
        }

        @Override
        public int size() {
            final Collection<V> coll = getMapping();
            return coll == null ? 0 : coll.size();
        }

        @Override
        public boolean contains(final Object obj) {
            final Collection<V> coll = getMapping();
            return coll == null ? false : coll.contains(obj);
        }

        @Override
        public boolean containsAll(final Collection<?> other) {
            final Collection<V> coll = getMapping();
            return coll == null ? false : coll.containsAll(other);
        }

        @Override
        public boolean isEmpty() {
            final Collection<V> coll = getMapping();
            return coll == null ? true : coll.isEmpty();
        }

        @Override
        public boolean remove(final Object item) {
            final Collection<V> coll = getMapping();
            if (coll == null) {
                return false;
            }

            final boolean result = coll.remove(item);
            if (coll.isEmpty()) {
                AbstractMultiValuedMap.this.remove(key);
            }
            return result;
        }

        @Override
        public boolean removeAll(final Collection<?> c) {
            final Collection<V> coll = getMapping();
            if (coll == null) {
                return false;
            }

            final boolean result = coll.removeAll(c);
            if (coll.isEmpty()) {
                AbstractMultiValuedMap.this.remove(key);
            }
            return result;
        }

        @Override
        public boolean retainAll(final Collection<?> c) {
            final Collection<V> coll = getMapping();
            if (coll == null) {
                return false;
            }

            final boolean result = coll.retainAll(c);
            if (coll.isEmpty()) {
                AbstractMultiValuedMap.this.remove(key);
            }
            return result;
        }

        @Override
        public Object[] toArray() {
            final Collection<V> coll = getMapping();
            if (coll == null) {
                return CollectionUtils.EMPTY_COLLECTION.toArray();
            }
            return coll.toArray();
        }

        @Override
        @SuppressWarnings("unchecked")
        public <T> T[] toArray(final T[] a) {
            final Collection<V> coll = getMapping();
            if (coll == null) {
                return (T[]) CollectionUtils.EMPTY_COLLECTION.toArray(a);
            }
            return coll.toArray(a);
        }

        @Override
        public String toString() {
            final Collection<V> coll = getMapping();
            if (coll == null) {
                return CollectionUtils.EMPTY_COLLECTION.toString();
            }
            return coll.toString();
        }

    }

    /**
     * Inner class that provides a MultiSet<K> keys view.
     */
    private class KeysMultiSet extends AbstractMultiSet<K> {

        @Override
        public boolean contains(final Object o) {
            return getMap().containsKey(o);
        }

        @Override
        public boolean isEmpty() {
            return getMap().isEmpty();
        }

        @Override
        public int size() {
            return AbstractMultiValuedMap.this.size();
        }

        @Override
        protected int uniqueElements() {
            return getMap().size();
        }

        @Override
        public int getCount(final Object object) {
            int count = 0;
            final Collection<V> col = AbstractMultiValuedMap.this.getMap().get(object);
            if (col != null) {
                count = col.size();
            }
            return count;
        }

        @Override
        protected Iterator<MultiSet.Entry<K>> createEntrySetIterator() {
            final MapEntryTransformer transformer = new MapEntryTransformer();
            return IteratorUtils.transformedIterator(map.entrySet().iterator(), transformer);
        }

        private final class MapEntryTransformer
            implements Transformer<Map.Entry<K, Collection<V>>, MultiSet.Entry<K>> {
            @Override
            public MultiSet.Entry<K> transform(final Map.Entry<K, Collection<V>> mapEntry) {
                return new AbstractMultiSet.AbstractEntry<K>() {
                    @Override
                    public K getElement() {
                        return mapEntry.getKey();
                    }

                    @Override
                    public int getCount() {
                        return mapEntry.getValue().size();
                    }
                };
            }
        }
    }

    /**
     * Inner class that provides the Entry<K, V> view
     */
    private class EntryValues extends AbstractCollection<Entry<K, V>> {

        @Override
        public Iterator<Entry<K, V>> iterator() {
            return new LazyIteratorChain<Entry<K, V>>() {

                final Collection<K> keysCol = new ArrayList<>(getMap().keySet());
                final Iterator<K> keyIterator = keysCol.iterator();

                @Override
                protected Iterator<? extends Entry<K, V>> nextIterator(final int count) {
                    if (!keyIterator.hasNext()) {
                        return null;
                    }
                    final K key = keyIterator.next();
                    final Transformer<V, Entry<K, V>> entryTransformer = new Transformer<V, Entry<K, V>>() {

                        @Override
                        public Entry<K, V> transform(final V input) {
                            return new MultiValuedMapEntry(key, input);
                        }

                    };
                    return new TransformIterator<>(new ValuesIterator(key), entryTransformer);
                }
            };
        }

        @Override
        public int size() {
            return AbstractMultiValuedMap.this.size();
        }

    }

    /**
     * Inner class for MultiValuedMap Entries.
     */
    private class MultiValuedMapEntry extends AbstractMapEntry<K, V> {

        public MultiValuedMapEntry(final K key, final V value) {
            super(key, value);
        }

        @Override
        public V setValue(final V value) {
            throw new UnsupportedOperationException();
        }

    }

    /**
     * Inner class for MapIterator.
     */
    private class MultiValuedMapIterator implements MapIterator<K, V> {

        private final Iterator<Entry<K, V>> it;

        private Entry<K, V> current = null;

        public MultiValuedMapIterator() {
            this.it = AbstractMultiValuedMap.this.entries().iterator();
        }

        @Override
        public boolean hasNext() {
            return it.hasNext();
        }

        @Override
        public K next() {
            current = it.next();
            return current.getKey();
        }

        @Override
        public K getKey() {
            if (current == null) {
                throw new IllegalStateException();
            }
            return current.getKey();
        }

        @Override
        public V getValue() {
            if (current == null) {
                throw new IllegalStateException();
            }
            return current.getValue();
        }

        @Override
        public void remove() {
            it.remove();
        }

        @Override
        public V setValue(final V value) {
            if (current == null) {
                throw new IllegalStateException();
            }
            return current.setValue(value);
        }

    }

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
            return AbstractMultiValuedMap.this.size();
        }

        @Override
        public void clear() {
            AbstractMultiValuedMap.this.clear();
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
            this.values = getMap().get(key);
            this.iterator = values.iterator();
        }

        @Override
        public void remove() {
            iterator.remove();
            if (values.isEmpty()) {
                AbstractMultiValuedMap.this.remove(key);
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
     * Inner class that provides the AsMap view.
     */
    private class AsMap extends AbstractMap<K, Collection<V>> {
        final transient Map<K, Collection<V>> decoratedMap;

        AsMap(final Map<K, Collection<V>> map) {
          this.decoratedMap = map;
        }

        @Override
        public Set<Map.Entry<K, Collection<V>>> entrySet() {
          return new AsMapEntrySet();
        }

        @Override
        public boolean containsKey(final Object key) {
            return decoratedMap.containsKey(key);
        }

        @Override
        public Collection<V> get(final Object key) {
          final Collection<V> collection = decoratedMap.get(key);
          if (collection == null) {
            return null;
          }
          @SuppressWarnings("unchecked")
        final
          K k = (K) key;
          return wrappedCollection(k);
        }

        @Override
        public Set<K> keySet() {
          return AbstractMultiValuedMap.this.keySet();
        }

        @Override
        public int size() {
          return decoratedMap.size();
        }

        @Override
        public Collection<V> remove(final Object key) {
          final Collection<V> collection = decoratedMap.remove(key);
          if (collection == null) {
            return null;
          }

          final Collection<V> output = createCollection();
          output.addAll(collection);
          collection.clear();
          return output;
        }

        @Override
        public boolean equals(final Object object) {
          return this == object || decoratedMap.equals(object);
        }

        @Override
        public int hashCode() {
          return decoratedMap.hashCode();
        }

        @Override
        public String toString() {
          return decoratedMap.toString();
        }

        @Override
        public void clear() {
            AbstractMultiValuedMap.this.clear();
        }

        class AsMapEntrySet extends AbstractSet<Map.Entry<K, Collection<V>>> {

            @Override
            public Iterator<Map.Entry<K, Collection<V>>> iterator() {
                return new AsMapEntrySetIterator(decoratedMap.entrySet().iterator());
            }

            @Override
            public int size() {
              return AsMap.this.size();
            }

            @Override
            public void clear() {
                AsMap.this.clear();
            }

            @Override
            public boolean contains(final Object o) {
                return decoratedMap.entrySet().contains(o);
            }

            @Override
            public boolean remove(final Object o) {
                if (!contains(o)) {
                    return false;
                }
                final Map.Entry<?, ?> entry = (Map.Entry<?, ?>) o;
                AbstractMultiValuedMap.this.remove(entry.getKey());
                return true;
            }
        }

        /**
         * EntrySet iterator for the asMap view.
         */
        class AsMapEntrySetIterator extends AbstractIteratorDecorator<Map.Entry<K, Collection<V>>> {

            AsMapEntrySetIterator(final Iterator<Map.Entry<K, Collection<V>>> iterator) {
                super(iterator);
            }

            @Override
            public Map.Entry<K, Collection<V>> next() {
                final Map.Entry<K, Collection<V>> entry = super.next();
                final K key = entry.getKey();
                return new UnmodifiableMapEntry<>(key, wrappedCollection(key));
            }
        }
    }

    //-----------------------------------------------------------------------
    /**
     * Write the map out using a custom routine.
     * @param out the output stream
     * @throws IOException any of the usual I/O related exceptions
     */
    protected void doWriteObject(final ObjectOutputStream out) throws IOException {
        out.writeInt(map.size());
        for (final Map.Entry<K, Collection<V>> entry : map.entrySet()) {
            out.writeObject(entry.getKey());
            out.writeInt(entry.getValue().size());
            for (final V value : entry.getValue()) {
                out.writeObject(value);
            }
        }
    }

    /**
     * Read the map in using a custom routine.
     * @param in the input stream
     * @throws IOException any of the usual I/O related exceptions
     * @throws ClassNotFoundException if the stream contains an object which class can not be loaded
     * @throws ClassCastException if the stream does not contain the correct objects
     */
    protected void doReadObject(final ObjectInputStream in)
            throws IOException, ClassNotFoundException {
        final int entrySize = in.readInt();
        for (int i = 0; i < entrySize; i++) {
            @SuppressWarnings("unchecked") // This will fail at runtime if the stream is incorrect
            final K key = (K) in.readObject();
            final Collection<V> values = get(key);
            final int valueSize = in.readInt();
            for (int j = 0; j < valueSize; j++) {
                @SuppressWarnings("unchecked") // see above
                final
                V value = (V) in.readObject();
                values.add(value);
            }
        }
    }

}
