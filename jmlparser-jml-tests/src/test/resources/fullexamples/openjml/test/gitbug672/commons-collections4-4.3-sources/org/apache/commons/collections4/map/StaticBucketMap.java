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

import java.util.AbstractCollection;
import java.util.AbstractSet;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;

import org.apache.commons.collections4.KeyValue;

/**
 * A StaticBucketMap is an efficient, thread-safe implementation of
 * <code>java.util.Map</code> that performs well in in a highly
 * thread-contentious environment.  The map supports very efficient
 * {@link #get(Object) get}, {@link #put(Object,Object) put},
 * {@link #remove(Object) remove} and {@link #containsKey(Object) containsKey}
 * operations, assuming (approximate) uniform hashing and
 * that the number of entries does not exceed the number of buckets.  If the
 * number of entries exceeds the number of buckets or if the hash codes of the
 * objects are not uniformly distributed, these operations have a worst case
 * scenario that is proportional to the number of elements in the map
 * (<i>O(n)</i>).<p>
 *
 * Each bucket in the hash table has its own monitor, so two threads can
 * safely operate on the map at the same time, often without incurring any
 * monitor contention.  This means that you don't have to wrap instances
 * of this class with {@link java.util.Collections#synchronizedMap(Map)};
 * instances are already thread-safe.  Unfortunately, however, this means
 * that this map implementation behaves in ways you may find disconcerting.
 * Bulk operations, such as {@link #putAll(Map) putAll} or the
 * {@link Collection#retainAll(Collection) retainAll} operation in collection
 * views, are <i>not</i> atomic.  If two threads are simultaneously
 * executing
 *
 * <pre>
 *   staticBucketMapInstance.putAll(map);
 * </pre>
 *
 * and
 *
 * <pre>
 *   staticBucketMapInstance.entrySet().removeAll(map.entrySet());
 * </pre>
 *
 * then the results are generally random.  Those two statement could cancel
 * each other out, leaving <code>staticBucketMapInstance</code> essentially
 * unchanged, or they could leave some random subset of <code>map</code> in
 * <code>staticBucketMapInstance</code>.<p>
 *
 * Also, much like an encyclopedia, the results of {@link #size()} and
 * {@link #isEmpty()} are out-of-date as soon as they are produced.<p>
 *
 * The iterators returned by the collection views of this class are <i>not</i>
 * fail-fast.  They will <i>never</i> raise a
 * {@link java.util.ConcurrentModificationException}.  Keys and values
 * added to the map after the iterator is created do not necessarily appear
 * during iteration.  Similarly, the iterator does not necessarily fail to
 * return keys and values that were removed after the iterator was created.<p>
 *
 * Finally, unlike {@link java.util.HashMap}-style implementations, this
 * class <i>never</i> rehashes the map.  The number of buckets is fixed
 * at construction time and never altered.  Performance may degrade if
 * you do not allocate enough buckets upfront.<p>
 *
 * The {@link #atomic(Runnable)} method is provided to allow atomic iterations
 * and bulk operations; however, overuse of {@link #atomic(Runnable) atomic}
 * will basically result in a map that's slower than an ordinary synchronized
 * {@link java.util.HashMap}.
 *
 * Use this class if you do not require reliable bulk operations and
 * iterations, or if you can make your own guarantees about how bulk
 * operations will affect the map.<p>
 *
 * @param <K> the type of the keys in this map
 * @param <V> the type of the values in this map
 * @since 3.0 (previously in main package v2.1)
 */
public final class StaticBucketMap<K, V> extends AbstractIterableMap<K, V> {

    /** The default number of buckets to use */
    private static final int DEFAULT_BUCKETS = 255;
    /** The array of buckets, where the actual data is held */
    private final Node<K, V>[] buckets;
    /** The matching array of locks */
    private final Lock[] locks;

    /**
     * Initializes the map with the default number of buckets (255).
     */
    public StaticBucketMap() {
        this(DEFAULT_BUCKETS);
    }

    /**
     * Initializes the map with a specified number of buckets.  The number
     * of buckets is never below 17, and is always an odd number (StaticBucketMap
     * ensures this). The number of buckets is inversely proportional to the
     * chances for thread contention.  The fewer buckets, the more chances for
     * thread contention.  The more buckets the fewer chances for thread
     * contention.
     *
     * @param numBuckets  the number of buckets for this map
     */
    @SuppressWarnings("unchecked")
    public StaticBucketMap(final int numBuckets) {
        int size = Math.max(17, numBuckets);

        // Ensure that bucketSize is never a power of 2 (to ensure maximal distribution)
        if (size % 2 == 0) {
            size--;
        }

        buckets = new Node[size];
        locks = new Lock[size];

        for (int i = 0; i < size; i++) {
            locks[i] = new Lock();
        }
    }

    //-----------------------------------------------------------------------
    /**
     * Determine the exact hash entry for the key.  The hash algorithm
     * is rather simplistic, but it does the job:
     *
     * <pre>
     *   He = |Hk mod n|
     * </pre>
     *
     * <p>
     *   He is the entry's hashCode, Hk is the key's hashCode, and n is
     *   the number of buckets.
     * </p>
     */
    private int getHash(final Object key) {
        if (key == null) {
            return 0;
        }
        int hash = key.hashCode();
        hash += ~(hash << 15);
        hash ^= (hash >>> 10);
        hash += (hash << 3);
        hash ^= (hash >>> 6);
        hash += ~(hash << 11);
        hash ^= (hash >>> 16);
        hash %= buckets.length;
        return (hash < 0) ? hash * -1 : hash;
    }

    /**
     * Gets the current size of the map.
     * The value is computed fresh each time the method is called.
     *
     * @return the current size
     */
    @Override
    public int size() {
        int cnt = 0;

        for (int i = 0; i < buckets.length; i++) {
            synchronized(locks[i]) {
                cnt += locks[i].size;
            }
        }
        return cnt;
    }

    /**
     * Checks if the size is currently zero.
     *
     * @return true if empty
     */
    @Override
    public boolean isEmpty() {
        return (size() == 0);
    }

    /**
     * Gets the value associated with the key.
     *
     * @param key  the key to retrieve
     * @return the associated value
     */
    @Override
    public V get(final Object key) {
        final int hash = getHash(key);

        synchronized (locks[hash]) {
            Node<K, V> n = buckets[hash];

            while (n != null) {
                if (n.key == key || (n.key != null && n.key.equals(key))) {
                    return n.value;
                }

                n = n.next;
            }
        }
        return null;
    }

    /**
     * Checks if the map contains the specified key.
     *
     * @param key  the key to check
     * @return true if found
     */
    @Override
    public boolean containsKey(final Object key) {
        final int hash = getHash(key);

        synchronized (locks[hash]) {
            Node<K, V> n = buckets[hash];

            while (n != null) {
                if (n.key == key || (n.key != null && n.key.equals(key))) {
                    return true;
                }

                n = n.next;
            }
        }
        return false;
    }

    /**
     * Checks if the map contains the specified value.
     *
     * @param value  the value to check
     * @return true if found
     */
    @Override
    public boolean containsValue(final Object value) {
        for (int i = 0; i < buckets.length; i++) {
            synchronized (locks[i]) {
                Node<K, V> n = buckets[i];

                while (n != null) {
                    if (n.value == value || (n.value != null && n.value.equals(value))) {
                        return true;
                    }

                    n = n.next;
                }
            }
        }
        return false;
    }

    //-----------------------------------------------------------------------
    /**
     * Puts a new key value mapping into the map.
     *
     * @param key  the key to use
     * @param value  the value to use
     * @return the previous mapping for the key
     */
    @Override
    public V put(final K key, final V value) {
        final int hash = getHash(key);

        synchronized (locks[hash]) {
            Node<K, V> n = buckets[hash];

            if (n == null) {
                n = new Node<>();
                n.key = key;
                n.value = value;
                buckets[hash] = n;
                locks[hash].size++;
                return null;
            }

            // Set n to the last node in the linked list.  Check each key along the way
            //  If the key is found, then change the value of that node and return
            //  the old value.
            for (Node<K, V> next = n; next != null; next = next.next) {
                n = next;

                if (n.key == key || (n.key != null && n.key.equals(key))) {
                    final V returnVal = n.value;
                    n.value = value;
                    return returnVal;
                }
            }

            // The key was not found in the current list of nodes, add it to the end
            //  in a new node.
            final Node<K, V> newNode = new Node<>();
            newNode.key = key;
            newNode.value = value;
            n.next = newNode;
            locks[hash].size++;
        }
        return null;
    }

    /**
     * Removes the specified key from the map.
     *
     * @param key  the key to remove
     * @return the previous value at this key
     */
    @Override
    public V remove(final Object key) {
        final int hash = getHash(key);

        synchronized (locks[hash]) {
            Node<K, V> n = buckets[hash];
            Node<K, V> prev = null;

            while (n != null) {
                if (n.key == key || (n.key != null && n.key.equals(key))) {
                    // Remove this node from the linked list of nodes.
                    if (null == prev) {
                        // This node was the head, set the next node to be the new head.
                        buckets[hash] = n.next;
                    } else {
                        // Set the next node of the previous node to be the node after this one.
                        prev.next = n.next;
                    }
                    locks[hash].size--;
                    return n.value;
                }

                prev = n;
                n = n.next;
            }
        }
        return null;
    }

    //-----------------------------------------------------------------------
    /**
     * Gets the key set.
     *
     * @return the key set
     */
    @Override
    public Set<K> keySet() {
        return new KeySet();
    }

    /**
     * Gets the values.
     *
     * @return the values
     */
    @Override
    public Collection<V> values() {
        return new Values();
    }

    /**
     * Gets the entry set.
     *
     * @return the entry set
     */
    @Override
    public Set<Map.Entry<K, V>> entrySet() {
        return new EntrySet();
    }

    //-----------------------------------------------------------------------
    /**
     * Puts all the entries from the specified map into this map.
     * This operation is <b>not atomic</b> and may have undesired effects.
     *
     * @param map  the map of entries to add
     */
    @Override
    public void putAll(final Map<? extends K, ? extends V> map) {
        for (final Map.Entry<? extends K, ? extends V> entry : map.entrySet()) {
            put(entry.getKey(), entry.getValue());
        }
    }

    /**
     * Clears the map of all entries.
     */
    @Override
    public void clear() {
        for (int i = 0; i < buckets.length; i++) {
            final Lock lock = locks[i];
            synchronized (lock) {
                buckets[i] = null;
                lock.size = 0;
            }
        }
    }

    /**
     * Compares this map to another, as per the Map specification.
     *
     * @param obj  the object to compare to
     * @return true if equal
     */
    @Override
    public boolean equals(final Object obj) {
        if (obj == this) {
            return true;
        }
        if (obj instanceof Map<?, ?> == false) {
            return false;
        }
        final Map<?, ?> other = (Map<?, ?>) obj;
        return entrySet().equals(other.entrySet());
    }

    /**
     * Gets the hash code, as per the Map specification.
     *
     * @return the hash code
     */
    @Override
    public int hashCode() {
        int hashCode = 0;

        for (int i = 0; i < buckets.length; i++) {
            synchronized (locks[i]) {
                Node<K, V> n = buckets[i];

                while (n != null) {
                    hashCode += n.hashCode();
                    n = n.next;
                }
            }
        }
        return hashCode;
    }

    //-----------------------------------------------------------------------
    /**
     * The Map.Entry for the StaticBucketMap.
     */
    private static final class Node<K, V> implements Map.Entry<K, V>, KeyValue<K, V> {
        protected K key;
        protected V value;
        protected Node<K, V> next;

        @Override
        public K getKey() {
            return key;
        }

        @Override
        public V getValue() {
            return value;
        }

        @Override
        public int hashCode() {
            return ((key == null ? 0 : key.hashCode()) ^
                    (value == null ? 0 : value.hashCode()));
        }

        @Override
        public boolean equals(final Object obj) {
            if (obj == this) {
                return true;
            }
            if (obj instanceof Map.Entry<?, ?> == false) {
                return false;
            }

            final Map.Entry<?, ?> e2 = (Map.Entry<?, ?>) obj;
            return (
                (key == null ? e2.getKey() == null : key.equals(e2.getKey())) &&
                (value == null ? e2.getValue() == null : value.equals(e2.getValue())));
        }

        @Override
        public V setValue(final V obj) {
            final V retVal = value;
            value = obj;
            return retVal;
        }
    }

    /**
     * The lock object, which also includes a count of the nodes in this lock.
     */
    private final static class Lock {
        public int size;
    }

    //-----------------------------------------------------------------------
    private class BaseIterator {
        private final ArrayList<Map.Entry<K, V>> current = new ArrayList<>();
        private int bucket;
        private Map.Entry<K, V> last;

        public boolean hasNext() {
            if (current.size() > 0) {
                return true;
            }
            while (bucket < buckets.length) {
                synchronized (locks[bucket]) {
                    Node<K, V> n = buckets[bucket];
                    while (n != null) {
                        current.add(n);
                        n = n.next;
                    }
                    bucket++;
                    if (current.size() > 0) {
                        return true;
                    }
                }
            }
            return false;
        }

        protected Map.Entry<K, V> nextEntry() {
            if (!hasNext()) {
                throw new NoSuchElementException();
            }
            last = current.remove(current.size() - 1);
            return last;
        }

        public void remove() {
            if (last == null) {
                throw new IllegalStateException();
            }
            StaticBucketMap.this.remove(last.getKey());
            last = null;
        }
    }

    private class EntryIterator extends BaseIterator implements Iterator<Map.Entry<K, V>> {

        @Override
        public Map.Entry<K, V> next() {
            return nextEntry();
        }

    }

    private class ValueIterator extends BaseIterator implements Iterator<V> {

        @Override
        public V next() {
            return nextEntry().getValue();
        }

    }

    private class KeyIterator extends BaseIterator implements Iterator<K> {

        @Override
        public K next() {
            return nextEntry().getKey();
        }

    }

    private class EntrySet extends AbstractSet<Map.Entry<K, V>> {

        @Override
        public int size() {
            return StaticBucketMap.this.size();
        }

        @Override
        public void clear() {
            StaticBucketMap.this.clear();
        }

        @Override
        public Iterator<Map.Entry<K, V>> iterator() {
            return new EntryIterator();
        }

        @Override
        public boolean contains(final Object obj) {
            final Map.Entry<?, ?> entry = (Map.Entry<?, ?>) obj;
            final int hash = getHash(entry.getKey());
            synchronized (locks[hash]) {
                for (Node<K, V> n = buckets[hash]; n != null; n = n.next) {
                    if (n.equals(entry)) {
                        return true;
                    }
                }
            }
            return false;
        }

        @Override
        public boolean remove(final Object obj) {
            if (obj instanceof Map.Entry<?, ?> == false) {
                return false;
            }
            final Map.Entry<?, ?> entry = (Map.Entry<?, ?>) obj;
            final int hash = getHash(entry.getKey());
            synchronized (locks[hash]) {
                for (Node<K, V> n = buckets[hash]; n != null; n = n.next) {
                    if (n.equals(entry)) {
                        StaticBucketMap.this.remove(n.getKey());
                        return true;
                    }
                }
            }
            return false;
        }

    }

    private class KeySet extends AbstractSet<K> {

        @Override
        public int size() {
            return StaticBucketMap.this.size();
        }

        @Override
        public void clear() {
            StaticBucketMap.this.clear();
        }

        @Override
        public Iterator<K> iterator() {
            return new KeyIterator();
        }

        @Override
        public boolean contains(final Object obj) {
            return StaticBucketMap.this.containsKey(obj);
        }

        @Override
        public boolean remove(final Object obj) {
            final int hash = getHash(obj);
            synchronized (locks[hash]) {
                for (Node<K, V> n = buckets[hash]; n != null; n = n.next) {
                    final Object k = n.getKey();
                    if ((k == obj) || ((k != null) && k.equals(obj))) {
                        StaticBucketMap.this.remove(k);
                        return true;
                    }
                }
            }
            return false;
        }

    }


    private class Values extends AbstractCollection<V> {

        @Override
        public int size() {
            return StaticBucketMap.this.size();
        }

        @Override
        public void clear() {
            StaticBucketMap.this.clear();
        }

        @Override
        public Iterator<V> iterator() {
            return new ValueIterator();
        }

    }

    /**
     *  Prevents any operations from occurring on this map while the
     *  given {@link Runnable} executes.  This method can be used, for
     *  instance, to execute a bulk operation atomically:
     *
     *  <pre>
     *    staticBucketMapInstance.atomic(new Runnable() {
     *        public void run() {
     *            staticBucketMapInstance.putAll(map);
     *        }
     *    });
     *  </pre>
     *
     *  It can also be used if you need a reliable iterator:
     *
     *  <pre>
     *    staticBucketMapInstance.atomic(new Runnable() {
     *        public void run() {
     *            Iterator iterator = staticBucketMapInstance.iterator();
     *            while (iterator.hasNext()) {
     *                foo(iterator.next();
     *            }
     *        }
     *    });
     *  </pre>
     *
     *  <b>Implementation note:</b> This method requires a lot of time
     *  and a ton of stack space.  Essentially a recursive algorithm is used
     *  to enter each bucket's monitor.  If you have twenty thousand buckets
     *  in your map, then the recursive method will be invoked twenty thousand
     *  times.  You have been warned.
     *
     *  @param r  the code to execute atomically
     */
    public void atomic(final Runnable r) {
        if (r == null) {
            throw new NullPointerException();
        }
        atomic(r, 0);
    }

    private void atomic(final Runnable r, final int bucket) {
        if (bucket >= buckets.length) {
            r.run();
            return;
        }
        synchronized (locks[bucket]) {
            atomic(r, bucket + 1);
        }
    }

}
