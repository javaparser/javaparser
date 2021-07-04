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
import java.util.AbstractSet;
import java.util.Collection;
import java.util.Iterator;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;

import org.apache.commons.collections4.IterableMap;
import org.apache.commons.collections4.MapIterator;
import org.apache.commons.collections4.ResettableIterator;
import org.apache.commons.collections4.iterators.EmptyIterator;
import org.apache.commons.collections4.iterators.EmptyMapIterator;

/**
 * A <code>Map</code> implementation that stores data in simple fields until
 * the size is greater than 3.
 * <p>
 * This map is designed for performance and can outstrip HashMap.
 * It also has good garbage collection characteristics.
 * <ul>
 * <li>Optimised for operation at size 3 or less.
 * <li>Still works well once size 3 exceeded.
 * <li>Gets at size 3 or less are about 0-10% faster than HashMap,
 * <li>Puts at size 3 or less are over 4 times faster than HashMap.
 * <li>Performance 5% slower than HashMap once size 3 exceeded once.
 * </ul>
 * The design uses two distinct modes of operation - flat and delegate.
 * While the map is size 3 or less, operations map straight onto fields using
 * switch statements. Once size 4 is reached, the map switches to delegate mode
 * and only switches back when cleared. In delegate mode, all operations are
 * forwarded straight to a HashMap resulting in the 5% performance loss.
 * <p>
 * The performance gains on puts are due to not needing to create a Map Entry
 * object. This is a large saving not only in performance but in garbage collection.
 * <p>
 * Whilst in flat mode this map is also easy for the garbage collector to dispatch.
 * This is because it contains no complex objects or arrays which slow the progress.
 * <p>
 * Do not use <code>Flat3Map</code> if the size is likely to grow beyond 3.
 * <p>
 * <strong>Note that Flat3Map is not synchronized and is not thread-safe.</strong>
 * If you wish to use this map from multiple threads concurrently, you must use
 * appropriate synchronization. The simplest approach is to wrap this map
 * using {@link java.util.Collections#synchronizedMap(Map)}. This class may throw
 * exceptions when accessed by concurrent threads without synchronization.
 *
 * @param <K> the type of the keys in this map
 * @param <V> the type of the values in this map
 * @since 3.0
 */
public class Flat3Map<K, V> implements IterableMap<K, V>, Serializable, Cloneable {

    /** Serialization version */
    private static final long serialVersionUID = -6701087419741928296L;

    /** The size of the map, used while in flat mode */
    private transient int size;
    /** Hash, used while in flat mode */
    private transient int hash1;
    /** Hash, used while in flat mode */
    private transient int hash2;
    /** Hash, used while in flat mode */
    private transient int hash3;
    /** Key, used while in flat mode */
    private transient K key1;
    /** Key, used while in flat mode */
    private transient K key2;
    /** Key, used while in flat mode */
    private transient K key3;
    /** Value, used while in flat mode */
    private transient V value1;
    /** Value, used while in flat mode */
    private transient V value2;
    /** Value, used while in flat mode */
    private transient V value3;
    /** Map, used while in delegate mode */
    private transient AbstractHashedMap<K, V> delegateMap;

    /**
     * Constructor.
     */
    public Flat3Map() {
        super();
    }

    /**
     * Constructor copying elements from another map.
     *
     * @param map  the map to copy
     * @throws NullPointerException if the map is null
     */
    public Flat3Map(final Map<? extends K, ? extends V> map) {
        super();
        putAll(map);
    }

    //-----------------------------------------------------------------------
    /**
     * Gets the value mapped to the key specified.
     *
     * @param key  the key
     * @return the mapped value, null if no match
     */
    @Override
    public V get(final Object key) {
        if (delegateMap != null) {
            return delegateMap.get(key);
        }
        if (key == null) {
            switch (size) {
                // drop through
                case 3:
                    if (key3 == null) {
                        return value3;
                    }
                case 2:
                    if (key2 == null) {
                        return value2;
                    }
                case 1:
                    if (key1 == null) {
                        return value1;
                    }
            }
        } else {
            if (size > 0) {
                final int hashCode = key.hashCode();
                switch (size) {
                    // drop through
                    case 3:
                        if (hash3 == hashCode && key.equals(key3)) {
                            return value3;
                        }
                    case 2:
                        if (hash2 == hashCode && key.equals(key2)) {
                            return value2;
                        }
                    case 1:
                        if (hash1 == hashCode && key.equals(key1)) {
                            return value1;
                        }
                }
            }
        }
        return null;
    }

    /**
     * Gets the size of the map.
     *
     * @return the size
     */
    @Override
    public int size() {
        if (delegateMap != null) {
            return delegateMap.size();
        }
        return size;
    }

    /**
     * Checks whether the map is currently empty.
     *
     * @return true if the map is currently size zero
     */
    @Override
    public boolean isEmpty() {
        return size() == 0;
    }

    //-----------------------------------------------------------------------
    /**
     * Checks whether the map contains the specified key.
     *
     * @param key  the key to search for
     * @return true if the map contains the key
     */
    @Override
    public boolean containsKey(final Object key) {
        if (delegateMap != null) {
            return delegateMap.containsKey(key);
        }
        if (key == null) {
            switch (size) {  // drop through
                case 3:
                    if (key3 == null) {
                        return true;
                    }
                case 2:
                    if (key2 == null) {
                        return true;
                    }
                case 1:
                    if (key1 == null) {
                        return true;
                    }
            }
        } else {
            if (size > 0) {
                final int hashCode = key.hashCode();
                switch (size) {  // drop through
                    case 3:
                        if (hash3 == hashCode && key.equals(key3)) {
                            return true;
                        }
                    case 2:
                        if (hash2 == hashCode && key.equals(key2)) {
                            return true;
                        }
                    case 1:
                        if (hash1 == hashCode && key.equals(key1)) {
                            return true;
                        }
                }
            }
        }
        return false;
    }

    /**
     * Checks whether the map contains the specified value.
     *
     * @param value  the value to search for
     * @return true if the map contains the key
     */
    @Override
    public boolean containsValue(final Object value) {
        if (delegateMap != null) {
            return delegateMap.containsValue(value);
        }
        if (value == null) {  // drop through
            switch (size) {
                case 3:
                    if (value3 == null) {
                        return true;
                    }
                case 2:
                    if (value2 == null) {
                        return true;
                    }
                case 1:
                    if (value1 == null) {
                        return true;
                    }
            }
        } else {
            switch (size) {  // drop through
                case 3:
                    if (value.equals(value3)) {
                        return true;
                    }
                case 2:
                    if (value.equals(value2)) {
                        return true;
                    }
                case 1:
                    if (value.equals(value1)) {
                        return true;
                    }
            }
        }
        return false;
    }

    //-----------------------------------------------------------------------
    /**
     * Puts a key-value mapping into this map.
     *
     * @param key  the key to add
     * @param value  the value to add
     * @return the value previously mapped to this key, null if none
     */
    @Override
    public V put(final K key, final V value) {
        if (delegateMap != null) {
            return delegateMap.put(key, value);
        }
        // change existing mapping
        if (key == null) {
            switch (size) {  // drop through
                case 3:
                    if (key3 == null) {
                        final V old = value3;
                        value3 = value;
                        return old;
                    }
                case 2:
                    if (key2 == null) {
                        final V old = value2;
                        value2 = value;
                        return old;
                    }
                case 1:
                    if (key1 == null) {
                        final V old = value1;
                        value1 = value;
                        return old;
                    }
            }
        } else {
            if (size > 0) {
                final int hashCode = key.hashCode();
                switch (size) {  // drop through
                    case 3:
                        if (hash3 == hashCode && key.equals(key3)) {
                            final V old = value3;
                            value3 = value;
                            return old;
                        }
                    case 2:
                        if (hash2 == hashCode && key.equals(key2)) {
                            final V old = value2;
                            value2 = value;
                            return old;
                        }
                    case 1:
                        if (hash1 == hashCode && key.equals(key1)) {
                            final V old = value1;
                            value1 = value;
                            return old;
                        }
                }
            }
        }

        // add new mapping
        switch (size) {
            default:
                convertToMap();
                delegateMap.put(key, value);
                return null;
            case 2:
                hash3 = key == null ? 0 : key.hashCode();
                key3 = key;
                value3 = value;
                break;
            case 1:
                hash2 = key == null ? 0 : key.hashCode();
                key2 = key;
                value2 = value;
                break;
            case 0:
                hash1 = key == null ? 0 : key.hashCode();
                key1 = key;
                value1 = value;
                break;
        }
        size++;
        return null;
    }

    /**
     * Puts all the values from the specified map into this map.
     *
     * @param map  the map to add
     * @throws NullPointerException if the map is null
     */
    @Override
    public void putAll(final Map<? extends K, ? extends V> map) {
        final int size = map.size();
        if (size == 0) {
            return;
        }
        if (delegateMap != null) {
            delegateMap.putAll(map);
            return;
        }
        if (size < 4) {
            for (final Map.Entry<? extends K, ? extends V> entry : map.entrySet()) {
                put(entry.getKey(), entry.getValue());
            }
        } else {
            convertToMap();
            delegateMap.putAll(map);
        }
    }

    /**
     * Converts the flat map data to a map.
     */
    private void convertToMap() {
        delegateMap = createDelegateMap();
        switch (size) {  // drop through
            case 3:
                delegateMap.put(key3, value3);
            case 2:
                delegateMap.put(key2, value2);
            case 1:
                delegateMap.put(key1, value1);
            case 0:
                break;
            default:
                throw new IllegalStateException("Invalid map index: " + size);
        }

        size = 0;
        hash1 = hash2 = hash3 = 0;
        key1 = key2 = key3 = null;
        value1 = value2 = value3 = null;
    }

    /**
     * Create an instance of the map used for storage when in delegation mode.
     * <p>
     * This can be overridden by subclasses to provide a different map implementation.
     * Not every AbstractHashedMap is suitable, identity and reference based maps
     * would be poor choices.
     *
     * @return a new AbstractHashedMap or subclass
     * @since 3.1
     */
    protected AbstractHashedMap<K, V> createDelegateMap() {
        return new HashedMap<>();
    }

    /**
     * Removes the specified mapping from this map.
     *
     * @param key  the mapping to remove
     * @return the value mapped to the removed key, null if key not in map
     */
    @Override
    public V remove(final Object key) {
        if (delegateMap != null) {
            return delegateMap.remove(key);
        }
        if (size == 0) {
            return null;
        }
        if (key == null) {
            switch (size) {  // drop through
                case 3:
                    if (key3 == null) {
                        final V old = value3;
                        hash3 = 0;
                        key3 = null;
                        value3 = null;
                        size = 2;
                        return old;
                    }
                    if (key2 == null) {
                        final V old = value2;
                        hash2 = hash3;
                        key2 = key3;
                        value2 = value3;
                        hash3 = 0;
                        key3 = null;
                        value3 = null;
                        size = 2;
                        return old;
                    }
                    if (key1 == null) {
                        final V old = value1;
                        hash1 = hash3;
                        key1 = key3;
                        value1 = value3;
                        hash3 = 0;
                        key3 = null;
                        value3 = null;
                        size = 2;
                        return old;
                    }
                    return null;
                case 2:
                    if (key2 == null) {
                        final V old = value2;
                        hash2 = 0;
                        key2 = null;
                        value2 = null;
                        size = 1;
                        return old;
                    }
                    if (key1 == null) {
                        final V old = value1;
                        hash1 = hash2;
                        key1 = key2;
                        value1 = value2;
                        hash2 = 0;
                        key2 = null;
                        value2 = null;
                        size = 1;
                        return old;
                    }
                    return null;
                case 1:
                    if (key1 == null) {
                        final V old = value1;
                        hash1 = 0;
                        key1 = null;
                        value1 = null;
                        size = 0;
                        return old;
                    }
            }
        } else {
            if (size > 0) {
                final int hashCode = key.hashCode();
                switch (size) {  // drop through
                    case 3:
                        if (hash3 == hashCode && key.equals(key3)) {
                            final V old = value3;
                            hash3 = 0;
                            key3 = null;
                            value3 = null;
                            size = 2;
                            return old;
                        }
                        if (hash2 == hashCode && key.equals(key2)) {
                            final V old = value2;
                            hash2 = hash3;
                            key2 = key3;
                            value2 = value3;
                            hash3 = 0;
                            key3 = null;
                            value3 = null;
                            size = 2;
                            return old;
                        }
                        if (hash1 == hashCode && key.equals(key1)) {
                            final V old = value1;
                            hash1 = hash3;
                            key1 = key3;
                            value1 = value3;
                            hash3 = 0;
                            key3 = null;
                            value3 = null;
                            size = 2;
                            return old;
                        }
                        return null;
                    case 2:
                        if (hash2 == hashCode && key.equals(key2)) {
                            final V old = value2;
                            hash2 = 0;
                            key2 = null;
                            value2 = null;
                            size = 1;
                            return old;
                        }
                        if (hash1 == hashCode && key.equals(key1)) {
                            final V old = value1;
                            hash1 = hash2;
                            key1 = key2;
                            value1 = value2;
                            hash2 = 0;
                            key2 = null;
                            value2 = null;
                            size = 1;
                            return old;
                        }
                        return null;
                    case 1:
                        if (hash1 == hashCode && key.equals(key1)) {
                            final V old = value1;
                            hash1 = 0;
                            key1 = null;
                            value1 = null;
                            size = 0;
                            return old;
                        }
                }
            }
        }
        return null;
    }

    /**
     * Clears the map, resetting the size to zero and nullifying references
     * to avoid garbage collection issues.
     */
    @Override
    public void clear() {
        if (delegateMap != null) {
            delegateMap.clear();  // should aid gc
            delegateMap = null;  // switch back to flat mode
        } else {
            size = 0;
            hash1 = hash2 = hash3 = 0;
            key1 = key2 = key3 = null;
            value1 = value2 = value3 = null;
        }
    }

    //-----------------------------------------------------------------------
    /**
     * Gets an iterator over the map.
     * Changes made to the iterator affect this map.
     * <p>
     * A MapIterator returns the keys in the map. It also provides convenient
     * methods to get the key and value, and set the value.
     * It avoids the need to create an entrySet/keySet/values object.
     * It also avoids creating the Map Entry object.
     *
     * @return the map iterator
     */
    @Override
    public MapIterator<K, V> mapIterator() {
        if (delegateMap != null) {
            return delegateMap.mapIterator();
        }
        if (size == 0) {
            return EmptyMapIterator.<K, V>emptyMapIterator();
        }
        return new FlatMapIterator<>(this);
    }

    /**
     * FlatMapIterator
     */
    static class FlatMapIterator<K, V> implements MapIterator<K, V>, ResettableIterator<K> {
        private final Flat3Map<K, V> parent;
        private int nextIndex = 0;
        private boolean canRemove = false;

        FlatMapIterator(final Flat3Map<K, V> parent) {
            super();
            this.parent = parent;
        }

        @Override
        public boolean hasNext() {
            return nextIndex < parent.size;
        }

        @Override
        public K next() {
            if (hasNext() == false) {
                throw new NoSuchElementException(AbstractHashedMap.NO_NEXT_ENTRY);
            }
            canRemove = true;
            nextIndex++;
            return getKey();
        }

        @Override
        public void remove() {
            if (canRemove == false) {
                throw new IllegalStateException(AbstractHashedMap.REMOVE_INVALID);
            }
            parent.remove(getKey());
            nextIndex--;
            canRemove = false;
        }

        @Override
        public K getKey() {
            if (canRemove == false) {
                throw new IllegalStateException(AbstractHashedMap.GETKEY_INVALID);
            }
            switch (nextIndex) {
                case 3:
                    return parent.key3;
                case 2:
                    return parent.key2;
                case 1:
                    return parent.key1;
            }
            throw new IllegalStateException("Invalid map index: " + nextIndex);
        }

        @Override
        public V getValue() {
            if (canRemove == false) {
                throw new IllegalStateException(AbstractHashedMap.GETVALUE_INVALID);
            }
            switch (nextIndex) {
                case 3:
                    return parent.value3;
                case 2:
                    return parent.value2;
                case 1:
                    return parent.value1;
            }
            throw new IllegalStateException("Invalid map index: " + nextIndex);
        }

        @Override
        public V setValue(final V value) {
            if (canRemove == false) {
                throw new IllegalStateException(AbstractHashedMap.SETVALUE_INVALID);
            }
            final V old = getValue();
            switch (nextIndex) {
                case 3:
                    parent.value3 = value;
                    break;
                case 2:
                    parent.value2 = value;
                    break;
                case 1:
                    parent.value1 = value;
                    break;
                default:
                    throw new IllegalStateException("Invalid map index: " + nextIndex);
            }
            return old;
        }

        @Override
        public void reset() {
            nextIndex = 0;
            canRemove = false;
        }

        @Override
        public String toString() {
            if (canRemove) {
                return "Iterator[" + getKey() + "=" + getValue() + "]";
            }
            return "Iterator[]";
        }
    }

    /**
     * Gets the entrySet view of the map.
     * Changes made to the view affect this map.
     * <p>
     * NOTE: from 4.0, the returned Map Entry will be an independent object and will
     * not change anymore as the iterator progresses. To avoid this additional object
     * creation and simply iterate through the entries, use {@link #mapIterator()}.
     *
     * @return the entrySet view
     */
    @Override
    public Set<Map.Entry<K, V>> entrySet() {
        if (delegateMap != null) {
            return delegateMap.entrySet();
        }
        return new EntrySet<>(this);
    }

    /**
     * EntrySet
     */
    static class EntrySet<K, V> extends AbstractSet<Map.Entry<K, V>> {
        private final Flat3Map<K, V> parent;

        EntrySet(final Flat3Map<K, V> parent) {
            super();
            this.parent = parent;
        }

        @Override
        public int size() {
            return parent.size();
        }

        @Override
        public void clear() {
            parent.clear();
        }

        @Override
        public boolean remove(final Object obj) {
            if (obj instanceof Map.Entry == false) {
                return false;
            }
            final Map.Entry<?, ?> entry = (Map.Entry<?, ?>) obj;
            final Object key = entry.getKey();
            final boolean result = parent.containsKey(key);
            parent.remove(key);
            return result;
        }

        @Override
        public Iterator<Map.Entry<K, V>> iterator() {
            if (parent.delegateMap != null) {
                return parent.delegateMap.entrySet().iterator();
            }
            if (parent.size() == 0) {
                return EmptyIterator.<Map.Entry<K, V>>emptyIterator();
            }
            return new EntrySetIterator<>(parent);
        }
    }

    static class FlatMapEntry<K, V> implements Map.Entry<K, V> {
        private final Flat3Map<K, V> parent;
        private final int index;
        private volatile boolean removed;

        public FlatMapEntry(final Flat3Map<K, V> parent, final int index) {
            this.parent = parent;
            this.index = index;
            this.removed = false;
        }

        /**
         * Used by the iterator that created this entry to indicate that
         * {@link java.util.Iterator#remove()} has been called.
         * <p>
         * As a consequence, all subsequent call to {@link #getKey()},
         * {@link #setValue(Object)} and {@link #getValue()} will fail.
         *
         * @param flag the new value of the removed flag
         */
        void setRemoved(final boolean flag) {
            this.removed = flag;
        }

        @Override
        public K getKey() {
            if (removed) {
                throw new IllegalStateException(AbstractHashedMap.GETKEY_INVALID);
            }
            switch (index) {
                case 3:
                    return parent.key3;
                case 2:
                    return parent.key2;
                case 1:
                    return parent.key1;
            }
            throw new IllegalStateException("Invalid map index: " + index);
        }

        @Override
        public V getValue() {
            if (removed) {
                throw new IllegalStateException(AbstractHashedMap.GETVALUE_INVALID);
            }
            switch (index) {
                case 3:
                    return parent.value3;
                case 2:
                    return parent.value2;
                case 1:
                    return parent.value1;
            }
            throw new IllegalStateException("Invalid map index: " + index);
        }

        @Override
        public V setValue(final V value) {
            if (removed) {
                throw new IllegalStateException(AbstractHashedMap.SETVALUE_INVALID);
            }
            final V old = getValue();
            switch (index) {
                case 3:
                    parent.value3 = value;
                    break;
                case 2:
                    parent.value2 = value;
                    break;
                case 1:
                    parent.value1 = value;
                    break;
                default:
                    throw new IllegalStateException("Invalid map index: " + index);
            }
            return old;
        }

        @Override
        public boolean equals(final Object obj) {
            if (removed) {
                return false;
            }
            if (obj instanceof Map.Entry == false) {
                return false;
            }
            final Map.Entry<?, ?> other = (Map.Entry<?, ?>) obj;
            final Object key = getKey();
            final Object value = getValue();
            return (key == null ? other.getKey() == null : key.equals(other.getKey())) &&
                   (value == null ? other.getValue() == null : value.equals(other.getValue()));
        }

        @Override
        public int hashCode() {
            if (removed) {
                return 0;
            }
            final Object key = getKey();
            final Object value = getValue();
            return (key == null ? 0 : key.hashCode()) ^
                   (value == null ? 0 : value.hashCode());
        }

        @Override
        public String toString() {
            if (!removed) {
                return getKey() + "=" + getValue();
            }
            return "";
        }

    }

    static abstract class EntryIterator<K, V> {
        private final Flat3Map<K, V> parent;
        private int nextIndex = 0;
        private FlatMapEntry<K, V> currentEntry = null;

        /**
         * Create a new Flat3Map.EntryIterator.
         */
        public EntryIterator(final Flat3Map<K, V> parent) {
            this.parent = parent;
        }

        public boolean hasNext() {
            return nextIndex < parent.size;
        }

        public Map.Entry<K, V> nextEntry() {
            if (!hasNext()) {
                throw new NoSuchElementException(AbstractHashedMap.NO_NEXT_ENTRY);
            }
            currentEntry = new FlatMapEntry<>(parent, ++nextIndex);
            return currentEntry;
        }

        public void remove() {
            if (currentEntry == null) {
                throw new IllegalStateException(AbstractHashedMap.REMOVE_INVALID);
            }
            currentEntry.setRemoved(true);
            parent.remove(currentEntry.getKey());
            nextIndex--;
            currentEntry = null;
        }

    }

    /**
     * EntrySetIterator and MapEntry
     */
    static class EntrySetIterator<K, V> extends EntryIterator<K, V> implements Iterator<Map.Entry<K, V>> {
        EntrySetIterator(final Flat3Map<K, V> parent) {
            super(parent);
        }

        @Override
        public Map.Entry<K, V> next() {
            return nextEntry();
        }
    }

    /**
     * Gets the keySet view of the map.
     * Changes made to the view affect this map.
     * To simply iterate through the keys, use {@link #mapIterator()}.
     *
     * @return the keySet view
     */
    @Override
    public Set<K> keySet() {
        if (delegateMap != null) {
            return delegateMap.keySet();
        }
        return new KeySet<>(this);
    }

    /**
     * KeySet
     */
    static class KeySet<K> extends AbstractSet<K> {
        private final Flat3Map<K, ?> parent;

        KeySet(final Flat3Map<K, ?> parent) {
            super();
            this.parent = parent;
        }

        @Override
        public int size() {
            return parent.size();
        }

        @Override
        public void clear() {
            parent.clear();
        }

        @Override
        public boolean contains(final Object key) {
            return parent.containsKey(key);
        }

        @Override
        public boolean remove(final Object key) {
            final boolean result = parent.containsKey(key);
            parent.remove(key);
            return result;
        }

        @Override
        public Iterator<K> iterator() {
            if (parent.delegateMap != null) {
                return parent.delegateMap.keySet().iterator();
            }
            if (parent.size() == 0) {
                return EmptyIterator.<K>emptyIterator();
            }
            return new KeySetIterator<>(parent);
        }
    }

    /**
     * KeySetIterator
     */
    static class KeySetIterator<K> extends EntryIterator<K, Object> implements Iterator<K>{

        @SuppressWarnings("unchecked")
        KeySetIterator(final Flat3Map<K, ?> parent) {
            super((Flat3Map<K, Object>) parent);
        }

        @Override
        public K next() {
            return nextEntry().getKey();
        }
    }

    /**
     * Gets the values view of the map.
     * Changes made to the view affect this map.
     * To simply iterate through the values, use {@link #mapIterator()}.
     *
     * @return the values view
     */
    @Override
    public Collection<V> values() {
        if (delegateMap != null) {
            return delegateMap.values();
        }
        return new Values<>(this);
    }

    /**
     * Values
     */
    static class Values<V> extends AbstractCollection<V> {
        private final Flat3Map<?, V> parent;

        Values(final Flat3Map<?, V> parent) {
            super();
            this.parent = parent;
        }

        @Override
        public int size() {
            return parent.size();
        }

        @Override
        public void clear() {
            parent.clear();
        }

        @Override
        public boolean contains(final Object value) {
            return parent.containsValue(value);
        }

        @Override
        public Iterator<V> iterator() {
            if (parent.delegateMap != null) {
                return parent.delegateMap.values().iterator();
            }
            if (parent.size() == 0) {
                return EmptyIterator.<V>emptyIterator();
            }
            return new ValuesIterator<>(parent);
        }
    }

    /**
     * ValuesIterator
     */
    static class ValuesIterator<V> extends EntryIterator<Object, V> implements Iterator<V> {

        @SuppressWarnings("unchecked")
        ValuesIterator(final Flat3Map<?, V> parent) {
            super((Flat3Map<Object, V>) parent);
        }

        @Override
        public V next() {
            return nextEntry().getValue();
        }
    }

    //-----------------------------------------------------------------------
    /**
     * Write the map out using a custom routine.
     *
     * @param out  the output stream
     * @throws IOException if an error occurs while writing to the stream
     */
    private void writeObject(final ObjectOutputStream out) throws IOException {
        out.defaultWriteObject();
        out.writeInt(size());
        for (final MapIterator<?, ?> it = mapIterator(); it.hasNext();) {
            out.writeObject(it.next());  // key
            out.writeObject(it.getValue());  // value
        }
    }

    /**
     * Read the map in using a custom routine.
     *
     * @param in the input stream
     * @throws IOException if an error occurs while reading from the stream
     * @throws ClassNotFoundException if an object read from the stream can not be loaded
     */
    @SuppressWarnings("unchecked")
    private void readObject(final ObjectInputStream in) throws IOException, ClassNotFoundException {
        in.defaultReadObject();
        final int count = in.readInt();
        if (count > 3) {
            delegateMap = createDelegateMap();
        }
        for (int i = count; i > 0; i--) {
            put((K) in.readObject(), (V) in.readObject());
        }
    }

    //-----------------------------------------------------------------------
    /**
     * Clones the map without cloning the keys or values.
     *
     * @return a shallow clone
     * @since 3.1
     */
    @Override
    @SuppressWarnings("unchecked")
    public Flat3Map<K, V> clone() {
        try {
            final Flat3Map<K, V> cloned = (Flat3Map<K, V>) super.clone();
            if (cloned.delegateMap != null) {
                cloned.delegateMap = cloned.delegateMap.clone();
            }
            return cloned;
        } catch (final CloneNotSupportedException ex) {
            throw new InternalError();
        }
    }

    /**
     * Compares this map with another.
     *
     * @param obj  the object to compare to
     * @return true if equal
     */
    @Override
    public boolean equals(final Object obj) {
        if (obj == this) {
            return true;
        }
        if (delegateMap != null) {
            return delegateMap.equals(obj);
        }
        if (obj instanceof Map == false) {
            return false;
        }
        final Map<?, ?> other = (Map<?, ?>) obj;
        if (size != other.size()) {
            return false;
        }
        if (size > 0) {
            Object otherValue = null;
            switch (size) {  // drop through
                case 3:
                    if (other.containsKey(key3) == false) {
                        return false;
                    }
                    otherValue = other.get(key3);
                    if (value3 == null ? otherValue != null : !value3.equals(otherValue)) {
                        return false;
                    }
                case 2:
                    if (other.containsKey(key2) == false) {
                        return false;
                    }
                    otherValue = other.get(key2);
                    if (value2 == null ? otherValue != null : !value2.equals(otherValue)) {
                        return false;
                    }
                case 1:
                    if (other.containsKey(key1) == false) {
                        return false;
                    }
                    otherValue = other.get(key1);
                    if (value1 == null ? otherValue != null : !value1.equals(otherValue)) {
                        return false;
                    }
            }
        }
        return true;
    }

    /**
     * Gets the standard Map hashCode.
     *
     * @return the hash code defined in the Map interface
     */
    @Override
    public int hashCode() {
        if (delegateMap != null) {
            return delegateMap.hashCode();
        }
        int total = 0;
        switch (size) {  // drop through
            case 3:
                total += hash3 ^ (value3 == null ? 0 : value3.hashCode());
            case 2:
                total += hash2 ^ (value2 == null ? 0 : value2.hashCode());
            case 1:
                total += hash1 ^ (value1 == null ? 0 : value1.hashCode());
            case 0:
                break;
            default:
                throw new IllegalStateException("Invalid map index: " + size);
        }
        return total;
    }

    /**
     * Gets the map as a String.
     *
     * @return a string version of the map
     */
    @Override
    public String toString() {
        if (delegateMap != null) {
            return delegateMap.toString();
        }
        if (size == 0) {
            return "{}";
        }
        final StringBuilder buf = new StringBuilder(128);
        buf.append('{');
        switch (size) {  // drop through
            case 3:
                buf.append(key3 == this ? "(this Map)" : key3);
                buf.append('=');
                buf.append(value3 == this ? "(this Map)" : value3);
                buf.append(',');
            case 2:
                buf.append(key2 == this ? "(this Map)" : key2);
                buf.append('=');
                buf.append(value2 == this ? "(this Map)" : value2);
                buf.append(',');
            case 1:
                buf.append(key1 == this ? "(this Map)" : key1);
                buf.append('=');
                buf.append(value1 == this ? "(this Map)" : value1);
                break;
            // case 0: has already been dealt with
            default:
                throw new IllegalStateException("Invalid map index: " + size);
        }
        buf.append('}');
        return buf.toString();
    }

}
