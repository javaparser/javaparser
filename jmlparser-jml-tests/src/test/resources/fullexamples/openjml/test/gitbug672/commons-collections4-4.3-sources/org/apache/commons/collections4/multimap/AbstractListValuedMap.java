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

import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;

import org.apache.commons.collections4.ListUtils;
import org.apache.commons.collections4.ListValuedMap;

/**
 * Abstract implementation of the {@link ListValuedMap} interface to simplify
 * the creation of subclass implementations.
 * <p>
 * Subclasses specify a Map implementation to use as the internal storage and
 * the List implementation to use as values.
 *
 * @param <K> the type of the keys in this map
 * @param <V> the type of the values in this map
 * @since 4.1
 */
public abstract class AbstractListValuedMap<K, V> extends AbstractMultiValuedMap<K, V>
        implements ListValuedMap<K, V> {

    /**
     * Constructor needed for subclass serialisation.
     */
    protected AbstractListValuedMap() {
        super();
    }

    /**
     * A constructor that wraps, not copies
     *
     * @param map  the map to wrap, must not be null
     * @throws NullPointerException if the map is null
     */
    protected AbstractListValuedMap(final Map<K, ? extends List<V>> map) {
        super(map);
    }

    // -----------------------------------------------------------------------
    @Override
    @SuppressWarnings("unchecked")
    protected Map<K, List<V>> getMap() {
        return (Map<K, List<V>>) super.getMap();
    }

    /**
     * Creates a new value collection using the provided factory.
     * @return a new list
     */
    @Override
    protected abstract List<V> createCollection();

    // -----------------------------------------------------------------------
    /**
     * Gets the list of values associated with the specified key. This would
     * return an empty list in case the mapping is not present
     *
     * @param key  the key to retrieve
     * @return the {@code List} of values, will return an empty {@link List} for no mapping
     */
    @Override
    public List<V> get(final K key) {
        return wrappedCollection(key);
    }

    @Override
    List<V> wrappedCollection(final K key) {
        return new WrappedList(key);
    }

    /**
     * Removes all values associated with the specified key.
     * <p>
     * A subsequent <code>get(Object)</code> would return an empty list.
     *
     * @param key  the key to remove values from
     * @return the <code>List</code> of values removed, will return an empty,
     *   unmodifiable list for no mapping found.
     */
    @Override
    public List<V> remove(final Object key) {
        return ListUtils.emptyIfNull(getMap().remove(key));
    }

    // -----------------------------------------------------------------------
    /**
     * Wrapped list to handle add and remove on the list returned by get(object)
     */
    private class WrappedList extends WrappedCollection implements List<V> {

        public WrappedList(final K key) {
            super(key);
        }

        @Override
        protected List<V> getMapping() {
            return getMap().get(key);
        }

        @Override
        public void add(final int index, final V value) {
            List<V> list = getMapping();
            if (list == null) {
                list = createCollection();
                getMap().put(key, list);
            }
            list.add(index, value);
        }

        @Override
        public boolean addAll(final int index, final Collection<? extends V> c) {
            List<V> list = getMapping();
            if (list == null) {
                list = createCollection();
                final boolean changed = list.addAll(index, c);
                if (changed) {
                    getMap().put(key, list);
                }
                return changed;
            }
            return list.addAll(index, c);
        }

        @Override
        public V get(final int index) {
            final List<V> list = ListUtils.emptyIfNull(getMapping());
            return list.get(index);
        }

        @Override
        public int indexOf(final Object o) {
            final List<V> list = ListUtils.emptyIfNull(getMapping());
            return list.indexOf(o);
        }

        @Override
        public int lastIndexOf(final Object o) {
            final List<V> list = ListUtils.emptyIfNull(getMapping());
            return list.lastIndexOf(o);
        }

        @Override
        public ListIterator<V> listIterator() {
            return new ValuesListIterator(key);
        }

        @Override
        public ListIterator<V> listIterator(final int index) {
            return new ValuesListIterator(key, index);
        }

        @Override
        public V remove(final int index) {
            final List<V> list = ListUtils.emptyIfNull(getMapping());
            final V value = list.remove(index);
            if (list.isEmpty()) {
                AbstractListValuedMap.this.remove(key);
            }
            return value;
        }

        @Override
        public V set(final int index, final V value) {
            final List<V> list = ListUtils.emptyIfNull(getMapping());
            return list.set(index, value);
        }

        @Override
        public List<V> subList(final int fromIndex, final int toIndex) {
            final List<V> list = ListUtils.emptyIfNull(getMapping());
            return list.subList(fromIndex, toIndex);
        }

        @Override
        public boolean equals(final Object other) {
            final List<V> list = getMapping();
            if (list == null) {
                return Collections.emptyList().equals(other);
            }
            if (!(other instanceof List)) {
                return false;
            }
            final List<?> otherList = (List<?>) other;
            return ListUtils.isEqualList(list, otherList);
        }

        @Override
        public int hashCode() {
            final List<V> list = getMapping();
            return ListUtils.hashCodeForList(list);
        }

    }

    /** Values ListIterator */
    private class ValuesListIterator implements ListIterator<V> {

        private final K key;
        private List<V> values;
        private ListIterator<V> iterator;

        public ValuesListIterator(final K key) {
            this.key = key;
            this.values = ListUtils.emptyIfNull(getMap().get(key));
            this.iterator = values.listIterator();
        }

        public ValuesListIterator(final K key, final int index) {
            this.key = key;
            this.values = ListUtils.emptyIfNull(getMap().get(key));
            this.iterator = values.listIterator(index);
        }

        @Override
        public void add(final V value) {
            if (getMap().get(key) == null) {
                final List<V> list = createCollection();
                getMap().put(key, list);
                this.values = list;
                this.iterator = list.listIterator();
            }
            this.iterator.add(value);
        }

        @Override
        public boolean hasNext() {
            return iterator.hasNext();
        }

        @Override
        public boolean hasPrevious() {
            return iterator.hasPrevious();
        }

        @Override
        public V next() {
            return iterator.next();
        }

        @Override
        public int nextIndex() {
            return iterator.nextIndex();
        }

        @Override
        public V previous() {
            return iterator.previous();
        }

        @Override
        public int previousIndex() {
            return iterator.previousIndex();
        }

        @Override
        public void remove() {
            iterator.remove();
            if (values.isEmpty()) {
                getMap().remove(key);
            }
        }

        @Override
        public void set(final V value) {
            iterator.set(value);
        }

    }

}
