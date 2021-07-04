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
package org.apache.commons.collections4.collection;

import java.util.Collection;
import java.util.HashMap;

import org.apache.commons.collections4.MultiMap;
import org.apache.commons.collections4.Transformer;
import org.apache.commons.collections4.map.MultiValueMap;

/**
 * An IndexedCollection is a Map-like view onto a Collection. It accepts a
 * keyTransformer to define how the keys are converted from the values.
 * <p>
 * Modifications made to this decorator modify the index as well as the
 * decorated {@link Collection}. However, modifications to the underlying
 * {@link Collection} will not update the index and it will get out of sync.
 * <p>
 * If modification of the decorated {@link Collection} is unavoidable, then a
 * call to {@link #reindex()} will update the index to the current contents of
 * the {@link Collection}.
 *
 * @param <K> the type of object in the index.
 * @param <C> the type of object in the collection.
 *
 * @since 4.0
 */
public class IndexedCollection<K, C> extends AbstractCollectionDecorator<C> {

    // TODO: replace with MultiValuedMap

    /** Serialization version */
    private static final long serialVersionUID = -5512610452568370038L;

    /** The {@link Transformer} for generating index keys. */
    private final Transformer<C, K> keyTransformer;

    /** The map of indexes to collected objects. */
    private final MultiMap<K, C> index;

    /** The uniqueness constraint for the index. */
    private final boolean uniqueIndex;

    /**
     * Create an {@link IndexedCollection} for a unique index.
     * <p>
     * If an element is added, which maps to an existing key, an {@link IllegalArgumentException}
     * will be thrown.
     *
     * @param <K> the index object type.
     * @param <C> the collection type.
     * @param coll the decorated {@link Collection}.
     * @param keyTransformer the {@link Transformer} for generating index keys.
     * @return the created {@link IndexedCollection}.
     */
    public static <K, C> IndexedCollection<K, C> uniqueIndexedCollection(final Collection<C> coll,
                                                                         final Transformer<C, K> keyTransformer) {
        return new IndexedCollection<>(coll, keyTransformer,
                                           MultiValueMap.<K, C>multiValueMap(new HashMap<K, Collection<C>>()),
                                           true);
    }

    /**
     * Create an {@link IndexedCollection} for a non-unique index.
     *
     * @param <K> the index object type.
     * @param <C> the collection type.
     * @param coll the decorated {@link Collection}.
     * @param keyTransformer the {@link Transformer} for generating index keys.
     * @return the created {@link IndexedCollection}.
     */
    public static <K, C> IndexedCollection<K, C> nonUniqueIndexedCollection(final Collection<C> coll,
                                                                            final Transformer<C, K> keyTransformer) {
        return new IndexedCollection<>(coll, keyTransformer,
                                           MultiValueMap.<K, C>multiValueMap(new HashMap<K, Collection<C>>()),
                                           false);
    }

    /**
     * Create a {@link IndexedCollection}.
     *
     * @param coll  decorated {@link Collection}
     * @param keyTransformer  {@link Transformer} for generating index keys
     * @param map  map to use as index
     * @param uniqueIndex  if the index shall enforce uniqueness of index keys
     */
    public IndexedCollection(final Collection<C> coll, final Transformer<C, K> keyTransformer,
                             final MultiMap<K, C> map, final boolean uniqueIndex) {
        super(coll);
        this.keyTransformer = keyTransformer;
        this.index = map;
        this.uniqueIndex = uniqueIndex;
        reindex();
    }

    /**
     * {@inheritDoc}
     *
     * @throws IllegalArgumentException if the object maps to an existing key and the index
     *   enforces a uniqueness constraint
     */
    @Override
    public boolean add(final C object) {
        final boolean added = super.add(object);
        if (added) {
            addToIndex(object);
        }
        return added;
    }

    @Override
    public boolean addAll(final Collection<? extends C> coll) {
        boolean changed = false;
        for (final C c: coll) {
            changed |= add(c);
        }
        return changed;
    }

    @Override
    public void clear() {
        super.clear();
        index.clear();
    }

    /**
     * {@inheritDoc}
     * <p>
     * Note: uses the index for fast lookup
     */
    @SuppressWarnings("unchecked")
    @Override
    public boolean contains(final Object object) {
        return index.containsKey(keyTransformer.transform((C) object));
    }

    /**
     * {@inheritDoc}
     * <p>
     * Note: uses the index for fast lookup
     */
    @Override
    public boolean containsAll(final Collection<?> coll) {
        for (final Object o : coll) {
            if (!contains(o)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Get the element associated with the given key.
     * <p>
     * In case of a non-unique index, this method will return the first
     * value associated with the given key. To retrieve all elements associated
     * with a key, use {@link #values(Object)}.
     *
     * @param key  key to look up
     * @return element found
     * @see #values(Object)
     */
    public C get(final K key) {
        @SuppressWarnings("unchecked") // index is a MultiMap which returns a Collection
        final Collection<C> coll = (Collection<C>) index.get(key);
        return coll == null ? null : coll.iterator().next();
    }

    /**
     * Get all elements associated with the given key.
     *
     * @param key  key to look up
     * @return a collection of elements found, or null if {@code contains(key) == false}
     */
    @SuppressWarnings("unchecked") // index is a MultiMap which returns a Collection
    public Collection<C> values(final K key) {
        return (Collection<C>) index.get(key);
    }

    /**
     * Clears the index and re-indexes the entire decorated {@link Collection}.
     */
    public void reindex() {
        index.clear();
        for (final C c : decorated()) {
            addToIndex(c);
        }
    }

    @SuppressWarnings("unchecked")
    @Override
    public boolean remove(final Object object) {
        final boolean removed = super.remove(object);
        if (removed) {
            removeFromIndex((C) object);
        }
        return removed;
    }

    @Override
    public boolean removeAll(final Collection<?> coll) {
        boolean changed = false;
        for (final Object o : coll) {
            changed |= remove(o);
        }
        return changed;
    }

    @Override
    public boolean retainAll(final Collection<?> coll) {
        final boolean changed = super.retainAll(coll);
        if (changed) {
            reindex();
        }
        return changed;
    }

    //-----------------------------------------------------------------------

    /**
     * Provides checking for adding the index.
     *
     * @param object the object to index
     * @throws IllegalArgumentException if the object maps to an existing key and the index
     *   enforces a uniqueness constraint
     */
    private void addToIndex(final C object) {
        final K key = keyTransformer.transform(object);
        if (uniqueIndex && index.containsKey(key)) {
            throw new IllegalArgumentException("Duplicate key in uniquely indexed collection.");
        }
        index.put(key, object);
    }

    /**
     * Removes an object from the index.
     *
     * @param object the object to remove
     */
    private void removeFromIndex(final C object) {
        index.remove(keyTransformer.transform(object));
    }

}
