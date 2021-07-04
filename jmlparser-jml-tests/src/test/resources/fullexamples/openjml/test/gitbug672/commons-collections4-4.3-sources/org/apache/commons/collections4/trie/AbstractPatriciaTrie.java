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
package org.apache.commons.collections4.trie;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.util.AbstractCollection;
import java.util.AbstractMap;
import java.util.AbstractSet;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.ConcurrentModificationException;
import java.util.Iterator;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;
import java.util.SortedMap;

import org.apache.commons.collections4.OrderedMapIterator;

/**
 * This class implements the base PATRICIA algorithm and everything that
 * is related to the {@link Map} interface.
 *
 * @since 4.0
 */
abstract class AbstractPatriciaTrie<K, V> extends AbstractBitwiseTrie<K, V> {

    private static final long serialVersionUID = 5155253417231339498L;

    /** The root node of the {@link org.apache.commons.collections4.Trie}. */
    private transient TrieEntry<K, V> root = new TrieEntry<>(null, null, -1);

    /**
     * Each of these fields are initialized to contain an instance of the
     * appropriate view the first time this view is requested. The views are
     * stateless, so there's no reason to create more than one of each.
     */
    private transient volatile Set<K> keySet;
    private transient volatile Collection<V> values;
    private transient volatile Set<Map.Entry<K,V>> entrySet;

    /** The current size of the {@link org.apache.commons.collections4.Trie}. */
    private transient int size = 0;

    /**
     * The number of times this {@link org.apache.commons.collections4.Trie} has been modified.
     * It's used to detect concurrent modifications and fail-fast the {@link Iterator}s.
     */
    protected transient int modCount = 0;

    protected AbstractPatriciaTrie(final KeyAnalyzer<? super K> keyAnalyzer) {
        super(keyAnalyzer);
    }

    /**
     * Constructs a new {@link org.apache.commons.collections4.Trie org.apache.commons.collections4.Trie Trie}
     * using the given {@link KeyAnalyzer} and initializes the {@link org.apache.commons.collections4.Trie Trie}
     * with the values from the provided {@link Map}.
     */
    protected AbstractPatriciaTrie(final KeyAnalyzer<? super K> keyAnalyzer,
                                   final Map<? extends K, ? extends V> map) {
        super(keyAnalyzer);
        putAll(map);
    }

    //-----------------------------------------------------------------------
    @Override
    public void clear() {
        root.key = null;
        root.bitIndex = -1;
        root.value = null;

        root.parent = null;
        root.left = root;
        root.right = null;
        root.predecessor = root;

        size = 0;
        incrementModCount();
    }

    @Override
    public int size() {
        return size;
    }

    /**
     * A helper method to increment the {@link Trie} size and the modification counter.
     */
    void incrementSize() {
        size++;
        incrementModCount();
    }

    /**
     * A helper method to decrement the {@link Trie} size and increment the modification counter.
     */
    void decrementSize() {
        size--;
        incrementModCount();
    }

    /**
     * A helper method to increment the modification counter.
     */
    private void incrementModCount() {
        ++modCount;
    }

    @Override
    public V put(final K key, final V value) {
        if (key == null) {
            throw new NullPointerException("Key cannot be null");
        }

        final int lengthInBits = lengthInBits(key);

        // The only place to store a key with a length
        // of zero bits is the root node
        if (lengthInBits == 0) {
            if (root.isEmpty()) {
                incrementSize();
            } else {
                incrementModCount();
            }
            return root.setKeyValue(key, value);
        }

        final TrieEntry<K, V> found = getNearestEntryForKey(key, lengthInBits);
        if (compareKeys(key, found.key)) {
            if (found.isEmpty()) { // <- must be the root
                incrementSize();
            } else {
                incrementModCount();
            }
            return found.setKeyValue(key, value);
        }

        final int bitIndex = bitIndex(key, found.key);
        if (!KeyAnalyzer.isOutOfBoundsIndex(bitIndex)) {
            if (KeyAnalyzer.isValidBitIndex(bitIndex)) { // in 99.999...9% the case
                /* NEW KEY+VALUE TUPLE */
                final TrieEntry<K, V> t = new TrieEntry<>(key, value, bitIndex);
                addEntry(t, lengthInBits);
                incrementSize();
                return null;
            } else if (KeyAnalyzer.isNullBitKey(bitIndex)) {
                // A bits of the Key are zero. The only place to
                // store such a Key is the root Node!

                /* NULL BIT KEY */
                if (root.isEmpty()) {
                    incrementSize();
                } else {
                    incrementModCount();
                }
                return root.setKeyValue(key, value);

            } else if (KeyAnalyzer.isEqualBitKey(bitIndex)) {
                // This is a very special and rare case.

                /* REPLACE OLD KEY+VALUE */
                if (found != root) { // NOPMD
                    incrementModCount();
                    return found.setKeyValue(key, value);
                }
            }
        }

        throw new IllegalArgumentException("Failed to put: " + key + " -> " + value + ", " + bitIndex);
    }

    /**
     * Adds the given {@link TrieEntry} to the {@link Trie}.
     */
    TrieEntry<K, V> addEntry(final TrieEntry<K, V> entry, final int lengthInBits) {
        TrieEntry<K, V> current = root.left;
        TrieEntry<K, V> path = root;
        while(true) {
            if (current.bitIndex >= entry.bitIndex
                    || current.bitIndex <= path.bitIndex) {
                entry.predecessor = entry;

                if (!isBitSet(entry.key, entry.bitIndex, lengthInBits)) {
                    entry.left = entry;
                    entry.right = current;
                } else {
                    entry.left = current;
                    entry.right = entry;
                }

                entry.parent = path;
                if (current.bitIndex >= entry.bitIndex) {
                    current.parent = entry;
                }

                // if we inserted an uplink, set the predecessor on it
                if (current.bitIndex <= path.bitIndex) {
                    current.predecessor = entry;
                }

                if (path == root || !isBitSet(entry.key, path.bitIndex, lengthInBits)) {
                    path.left = entry;
                } else {
                    path.right = entry;
                }

                return entry;
            }

            path = current;

            if (!isBitSet(entry.key, current.bitIndex, lengthInBits)) {
                current = current.left;
            } else {
                current = current.right;
            }
        }
    }

    @Override
    public V get(final Object k) {
        final TrieEntry<K, V> entry = getEntry(k);
        return entry != null ? entry.getValue() : null;
    }

    /**
     * Returns the entry associated with the specified key in the
     * PatriciaTrieBase.  Returns null if the map contains no mapping
     * for this key.
     * <p>
     * This may throw ClassCastException if the object is not of type K.
     */
    TrieEntry<K,V> getEntry(final Object k) {
        final K key = castKey(k);
        if (key == null) {
            return null;
        }

        final int lengthInBits = lengthInBits(key);
        final TrieEntry<K,V> entry = getNearestEntryForKey(key, lengthInBits);
        return !entry.isEmpty() && compareKeys(key, entry.key) ? entry : null;
    }

    /**
     * Returns the {@link java.util.Map.Entry} whose key is closest in a bitwise XOR
     * metric to the given key. This is NOT lexicographic closeness.
     * For example, given the keys:
     *
     * <ol>
     * <li>D = 1000100
     * <li>H = 1001000
     * <li>L = 1001100
     * </ol>
     *
     * If the {@link org.apache.commons.collections4.Trie} contained 'H' and 'L', a lookup of 'D' would
     * return 'L', because the XOR distance between D &amp; L is smaller
     * than the XOR distance between D &amp; H.
     *
     * @param key  the key to use in the search
     * @return the {@link java.util.Map.Entry} whose key is closest in a bitwise XOR metric
     *   to the provided key
     */
    public Map.Entry<K, V> select(final K key) {
        final int lengthInBits = lengthInBits(key);
        final Reference<Map.Entry<K, V>> reference = new Reference<>();
        if (!selectR(root.left, -1, key, lengthInBits, reference)) {
            return reference.get();
        }
        return null;
    }

    /**
     * Returns the key that is closest in a bitwise XOR metric to the
     * provided key. This is NOT lexicographic closeness!
     *
     * For example, given the keys:
     *
     * <ol>
     * <li>D = 1000100
     * <li>H = 1001000
     * <li>L = 1001100
     * </ol>
     *
     * If the {@link org.apache.commons.collections4.Trie} contained 'H' and 'L', a lookup of 'D' would
     * return 'L', because the XOR distance between D &amp; L is smaller
     * than the XOR distance between D &amp; H.
     *
     * @param key  the key to use in the search
     * @return the key that is closest in a bitwise XOR metric to the provided key
     */
    public K selectKey(final K key) {
        final Map.Entry<K, V> entry = select(key);
        if (entry == null) {
            return null;
        }
        return entry.getKey();
    }

    /**
     * Returns the value whose key is closest in a bitwise XOR metric to
     * the provided key. This is NOT lexicographic closeness!
     *
     * For example, given the keys:
     *
     * <ol>
     * <li>D = 1000100
     * <li>H = 1001000
     * <li>L = 1001100
     * </ol>
     *
     * If the {@link org.apache.commons.collections4.Trie} contained 'H' and 'L', a lookup of 'D' would
     * return 'L', because the XOR distance between D &amp; L is smaller
     * than the XOR distance between D &amp; H.
     *
     * @param key  the key to use in the search
     * @return the value whose key is closest in a bitwise XOR metric
     * to the provided key
     */
    public V selectValue(final K key) {
        final Map.Entry<K, V> entry = select(key);
        if (entry == null) {
            return null;
        }
        return entry.getValue();
    }

    /**
     * This is equivalent to the other {@link #selectR(TrieEntry, int, Object, int, Cursor, Reference)}
     * method but without its overhead because we're selecting only one best matching Entry from the {@link Trie}.
     */
    private boolean selectR(final TrieEntry<K, V> h, final int bitIndex,
                            final K key, final int lengthInBits,
                            final Reference<Map.Entry<K, V>> reference) {

        if (h.bitIndex <= bitIndex) {
            // If we hit the root Node and it is empty
            // we have to look for an alternative best
            // matching node.
            if (!h.isEmpty()) {
                reference.set(h);
                return false;
            }
            return true;
        }

        if (!isBitSet(key, h.bitIndex, lengthInBits)) {
            if (selectR(h.left, h.bitIndex, key, lengthInBits, reference)) {
                return selectR(h.right, h.bitIndex, key, lengthInBits, reference);
            }
        } else {
            if (selectR(h.right, h.bitIndex, key, lengthInBits, reference)) {
                return selectR(h.left, h.bitIndex, key, lengthInBits, reference);
            }
        }
        return false;
    }

    @Override
    public boolean containsKey(final Object k) {
        if (k == null) {
            return false;
        }

        final K key = castKey(k);
        final int lengthInBits = lengthInBits(key);
        final TrieEntry<K, V> entry = getNearestEntryForKey(key, lengthInBits);
        return !entry.isEmpty() && compareKeys(key, entry.key);
    }

    @Override
    public Set<Map.Entry<K,V>> entrySet() {
        if (entrySet == null) {
            entrySet = new EntrySet();
        }
        return entrySet;
    }

    @Override
    public Set<K> keySet() {
        if (keySet == null) {
            keySet = new KeySet();
        }
        return keySet;
    }

    @Override
    public Collection<V> values() {
        if (values == null) {
            values = new Values();
        }
        return values;
    }

    /**
     * {@inheritDoc}
     *
     * @throws ClassCastException if provided key is of an incompatible type
     */
    @Override
    public V remove(final Object k) {
        if (k == null) {
            return null;
        }

        final K key = castKey(k);
        final int lengthInBits = lengthInBits(key);
        TrieEntry<K, V> current = root.left;
        TrieEntry<K, V> path = root;
        while (true) {
            if (current.bitIndex <= path.bitIndex) {
                if (!current.isEmpty() && compareKeys(key, current.key)) {
                    return removeEntry(current);
                }
                return null;
            }

            path = current;

            if (!isBitSet(key, current.bitIndex, lengthInBits)) {
                current = current.left;
            } else {
                current = current.right;
            }
        }
    }

    /**
     * Returns the nearest entry for a given key.  This is useful
     * for finding knowing if a given key exists (and finding the value
     * for it), or for inserting the key.
     *
     * The actual get implementation. This is very similar to
     * selectR but with the exception that it might return the
     * root Entry even if it's empty.
     */
    TrieEntry<K, V> getNearestEntryForKey(final K key, final int lengthInBits) {
        TrieEntry<K, V> current = root.left;
        TrieEntry<K, V> path = root;
        while(true) {
            if (current.bitIndex <= path.bitIndex) {
                return current;
            }

            path = current;
            if (!isBitSet(key, current.bitIndex, lengthInBits)) {
                current = current.left;
            } else {
                current = current.right;
            }
        }
    }

    /**
     * Removes a single entry from the {@link Trie}.
     *
     * If we found a Key (Entry h) then figure out if it's
     * an internal (hard to remove) or external Entry (easy
     * to remove)
     */
    V removeEntry(final TrieEntry<K, V> h) {
        if (h != root) {
            if (h.isInternalNode()) {
                removeInternalEntry(h);
            } else {
                removeExternalEntry(h);
            }
        }

        decrementSize();
        return h.setKeyValue(null, null);
    }

    /**
     * Removes an external entry from the {@link Trie}.
     *
     * If it's an external Entry then just remove it.
     * This is very easy and straight forward.
     */
    private void removeExternalEntry(final TrieEntry<K, V> h) {
        if (h == root) {
            throw new IllegalArgumentException("Cannot delete root Entry!");
        } else if (!h.isExternalNode()) {
            throw new IllegalArgumentException(h + " is not an external Entry!");
        }

        final TrieEntry<K, V> parent = h.parent;
        final TrieEntry<K, V> child = h.left == h ? h.right : h.left;

        if (parent.left == h) {
            parent.left = child;
        } else {
            parent.right = child;
        }

        // either the parent is changing, or the predecessor is changing.
        if (child.bitIndex > parent.bitIndex) {
            child.parent = parent;
        } else {
            child.predecessor = parent;
        }

    }

    /**
     * Removes an internal entry from the {@link Trie}.
     *
     * If it's an internal Entry then "good luck" with understanding
     * this code. The Idea is essentially that Entry p takes Entry h's
     * place in the trie which requires some re-wiring.
     */
    private void removeInternalEntry(final TrieEntry<K, V> h) {
        if (h == root) {
            throw new IllegalArgumentException("Cannot delete root Entry!");
        } else if (!h.isInternalNode()) {
            throw new IllegalArgumentException(h + " is not an internal Entry!");
        }

        final TrieEntry<K, V> p = h.predecessor;

        // Set P's bitIndex
        p.bitIndex = h.bitIndex;

        // Fix P's parent, predecessor and child Nodes
        {
            final TrieEntry<K, V> parent = p.parent;
            final TrieEntry<K, V> child = p.left == h ? p.right : p.left;

            // if it was looping to itself previously,
            // it will now be pointed from it's parent
            // (if we aren't removing it's parent --
            //  in that case, it remains looping to itself).
            // otherwise, it will continue to have the same
            // predecessor.
            if (p.predecessor == p && p.parent != h) {
                p.predecessor = p.parent;
            }

            if (parent.left == p) {
                parent.left = child;
            } else {
                parent.right = child;
            }

            if (child.bitIndex > parent.bitIndex) {
                child.parent = parent;
            }
        }

        // Fix H's parent and child Nodes
        {
            // If H is a parent of its left and right child
            // then change them to P
            if (h.left.parent == h) {
                h.left.parent = p;
            }

            if (h.right.parent == h) {
                h.right.parent = p;
            }

            // Change H's parent
            if (h.parent.left == h) {
                h.parent.left = p;
            } else {
                h.parent.right = p;
            }
        }

        // Copy the remaining fields from H to P
        //p.bitIndex = h.bitIndex;
        p.parent = h.parent;
        p.left = h.left;
        p.right = h.right;

        // Make sure that if h was pointing to any uplinks,
        // p now points to them.
        if (isValidUplink(p.left, p)) {
            p.left.predecessor = p;
        }

        if (isValidUplink(p.right, p)) {
            p.right.predecessor = p;
        }
    }

    /**
     * Returns the entry lexicographically after the given entry.
     * If the given entry is null, returns the first node.
     */
    TrieEntry<K, V> nextEntry(final TrieEntry<K, V> node) {
        if (node == null) {
            return firstEntry();
        }
        return nextEntryImpl(node.predecessor, node, null);
    }

    /**
     * Scans for the next node, starting at the specified point, and using 'previous'
     * as a hint that the last node we returned was 'previous' (so we know not to return
     * it again).  If 'tree' is non-null, this will limit the search to the given tree.
     *
     * The basic premise is that each iteration can follow the following steps:
     *
     * 1) Scan all the way to the left.
     *   a) If we already started from this node last time, proceed to Step 2.
     *   b) If a valid uplink is found, use it.
     *   c) If the result is an empty node (root not set), break the scan.
     *   d) If we already returned the left node, break the scan.
     *
     * 2) Check the right.
     *   a) If we already returned the right node, proceed to Step 3.
     *   b) If it is a valid uplink, use it.
     *   c) Do Step 1 from the right node.
     *
     * 3) Back up through the parents until we encounter find a parent
     *    that we're not the right child of.
     *
     * 4) If there's no right child of that parent, the iteration is finished.
     *    Otherwise continue to Step 5.
     *
     * 5) Check to see if the right child is a valid uplink.
     *    a) If we already returned that child, proceed to Step 6.
     *       Otherwise, use it.
     *
     * 6) If the right child of the parent is the parent itself, we've
     *    already found & returned the end of the Trie, so exit.
     *
     * 7) Do Step 1 on the parent's right child.
     */
    TrieEntry<K, V> nextEntryImpl(final TrieEntry<K, V> start,
            final TrieEntry<K, V> previous, final TrieEntry<K, V> tree) {

        TrieEntry<K, V> current = start;

        // Only look at the left if this was a recursive or
        // the first check, otherwise we know we've already looked
        // at the left.
        if (previous == null || start != previous.predecessor) {
            while (!current.left.isEmpty()) {
                // stop traversing if we've already
                // returned the left of this node.
                if (previous == current.left) {
                    break;
                }

                if (isValidUplink(current.left, current)) {
                    return current.left;
                }

                current = current.left;
            }
        }

        // If there's no data at all, exit.
        if (current.isEmpty()) {
            return null;
        }

        // If we've already returned the left,
        // and the immediate right is null,
        // there's only one entry in the Trie
        // which is stored at the root.
        //
        //  / ("")   <-- root
        //  \_/  \
        //       null <-- 'current'
        //
        if (current.right == null) {
            return null;
        }

        // If nothing valid on the left, try the right.
        if (previous != current.right) {
            // See if it immediately is valid.
            if (isValidUplink(current.right, current)) {
                return current.right;
            }

            // Must search on the right's side if it wasn't initially valid.
            return nextEntryImpl(current.right, previous, tree);
        }

        // Neither left nor right are valid, find the first parent
        // whose child did not come from the right & traverse it.
        while (current == current.parent.right) {
            // If we're going to traverse to above the subtree, stop.
            if (current == tree) {
                return null;
            }

            current = current.parent;
        }

        // If we're on the top of the subtree, we can't go any higher.
        if (current == tree) {
            return null;
        }

        // If there's no right, the parent must be root, so we're done.
        if (current.parent.right == null) {
            return null;
        }

        // If the parent's right points to itself, we've found one.
        if (previous != current.parent.right
                && isValidUplink(current.parent.right, current.parent)) {
            return current.parent.right;
        }

        // If the parent's right is itself, there can't be any more nodes.
        if (current.parent.right == current.parent) {
            return null;
        }

        // We need to traverse down the parent's right's path.
        return nextEntryImpl(current.parent.right, previous, tree);
    }

    /**
     * Returns the first entry the {@link Trie} is storing.
     * <p>
     * This is implemented by going always to the left until
     * we encounter a valid uplink. That uplink is the first key.
     */
    TrieEntry<K, V> firstEntry() {
        // if Trie is empty, no first node.
        if (isEmpty()) {
            return null;
        }

        return followLeft(root);
    }

    /**
     * Goes left through the tree until it finds a valid node.
     */
    TrieEntry<K, V> followLeft(TrieEntry<K, V> node) {
        while(true) {
            TrieEntry<K, V> child = node.left;
            // if we hit root and it didn't have a node, go right instead.
            if (child.isEmpty()) {
                child = node.right;
            }

            if (child.bitIndex <= node.bitIndex) {
                return child;
            }

            node = child;
        }
    }

    //-----------------------------------------------------------------------

    @Override
    public Comparator<? super K> comparator() {
        return getKeyAnalyzer();
    }

    @Override
    public K firstKey() {
        if (size() == 0) {
            throw new NoSuchElementException();
        }
        return firstEntry().getKey();
    }

    @Override
    public K lastKey() {
        final TrieEntry<K, V> entry = lastEntry();
        if (entry != null) {
            return entry.getKey();
        }
        throw new NoSuchElementException();
    }

    @Override
    public K nextKey(final K key) {
        if (key == null) {
            throw new NullPointerException();
        }
        final TrieEntry<K, V> entry = getEntry(key);
        if (entry != null) {
            final TrieEntry<K, V> nextEntry = nextEntry(entry);
            return nextEntry != null ? nextEntry.getKey() : null;
        }
        return null;
    }

    @Override
    public K previousKey(final K key) {
        if (key == null) {
            throw new NullPointerException();
        }
        final TrieEntry<K, V> entry = getEntry(key);
        if (entry != null) {
            final TrieEntry<K, V> prevEntry = previousEntry(entry);
            return prevEntry != null ? prevEntry.getKey() : null;
        }
        return null;
    }

    @Override
    public OrderedMapIterator<K, V> mapIterator() {
        return new TrieMapIterator();
    }

    @Override
    public SortedMap<K, V> prefixMap(final K key) {
        return getPrefixMapByBits(key, 0, lengthInBits(key));
    }

    /**
     * Returns a view of this {@link Trie} of all elements that are prefixed
     * by the number of bits in the given Key.
     * <p>
     * The view that this returns is optimized to have a very efficient
     * {@link Iterator}. The {@link SortedMap#firstKey()},
     * {@link SortedMap#lastKey()} &amp; {@link Map#size()} methods must
     * iterate over all possible values in order to determine the results.
     * This information is cached until the PATRICIA {@link Trie} changes.
     * All other methods (except {@link Iterator}) must compare the given
     * key to the prefix to ensure that it is within the range of the view.
     * The {@link Iterator}'s remove method must also relocate the subtree
     * that contains the prefixes if the entry holding the subtree is
     * removed or changes. Changing the subtree takes O(K) time.
     *
     * @param key  the key to use in the search
     * @param offsetInBits  the prefix offset
     * @param lengthInBits  the number of significant prefix bits
     * @return a {@link SortedMap} view of this {@link Trie} with all elements whose
     *   key is prefixed by the search key
     */
    private SortedMap<K, V> getPrefixMapByBits(final K key, final int offsetInBits, final int lengthInBits) {

        final int offsetLength = offsetInBits + lengthInBits;
        if (offsetLength > lengthInBits(key)) {
            throw new IllegalArgumentException(offsetInBits + " + "
                    + lengthInBits + " > " + lengthInBits(key));
        }

        if (offsetLength == 0) {
            return this;
        }

        return new PrefixRangeMap(key, offsetInBits, lengthInBits);
    }

    @Override
    public SortedMap<K, V> headMap(final K toKey) {
        return new RangeEntryMap(null, toKey);
    }

    @Override
    public SortedMap<K, V> subMap(final K fromKey, final K toKey) {
        return new RangeEntryMap(fromKey, toKey);
    }

    @Override
    public SortedMap<K, V> tailMap(final K fromKey) {
        return new RangeEntryMap(fromKey, null);
    }

    /**
     * Returns an entry strictly higher than the given key,
     * or null if no such entry exists.
     */
    TrieEntry<K,V> higherEntry(final K key) {
        // TODO: Cleanup so that we don't actually have to add/remove from the
        //       tree.  (We do it here because there are other well-defined
        //       functions to perform the search.)
        final int lengthInBits = lengthInBits(key);

        if (lengthInBits == 0) {
            if (!root.isEmpty()) {
                // If data in root, and more after -- return it.
                if (size() > 1) {
                    return nextEntry(root);
                }
                // If no more after, no higher entry.
                return null;
            }
            // Root is empty & we want something after empty, return first.
            return firstEntry();
        }

        final TrieEntry<K, V> found = getNearestEntryForKey(key, lengthInBits);
        if (compareKeys(key, found.key)) {
            return nextEntry(found);
        }

        final int bitIndex = bitIndex(key, found.key);
        if (KeyAnalyzer.isValidBitIndex(bitIndex)) {
            final TrieEntry<K, V> added = new TrieEntry<>(key, null, bitIndex);
            addEntry(added, lengthInBits);
            incrementSize(); // must increment because remove will decrement
            final TrieEntry<K, V> ceil = nextEntry(added);
            removeEntry(added);
            modCount -= 2; // we didn't really modify it.
            return ceil;
        } else if (KeyAnalyzer.isNullBitKey(bitIndex)) {
            if (!root.isEmpty()) {
                return firstEntry();
            } else if (size() > 1) {
                return nextEntry(firstEntry());
            } else {
                return null;
            }
        } else if (KeyAnalyzer.isEqualBitKey(bitIndex)) {
            return nextEntry(found);
        }

        // we should have exited above.
        throw new IllegalStateException("invalid lookup: " + key);
    }

    /**
     * Returns a key-value mapping associated with the least key greater
     * than or equal to the given key, or null if there is no such key.
     */
    TrieEntry<K,V> ceilingEntry(final K key) {
        // Basically:
        // Follow the steps of adding an entry, but instead...
        //
        // - If we ever encounter a situation where we found an equal
        //   key, we return it immediately.
        //
        // - If we hit an empty root, return the first iterable item.
        //
        // - If we have to add a new item, we temporarily add it,
        //   find the successor to it, then remove the added item.
        //
        // These steps ensure that the returned value is either the
        // entry for the key itself, or the first entry directly after
        // the key.

        // TODO: Cleanup so that we don't actually have to add/remove from the
        //       tree.  (We do it here because there are other well-defined
        //       functions to perform the search.)
        final int lengthInBits = lengthInBits(key);

        if (lengthInBits == 0) {
            if (!root.isEmpty()) {
                return root;
            }
            return firstEntry();
        }

        final TrieEntry<K, V> found = getNearestEntryForKey(key, lengthInBits);
        if (compareKeys(key, found.key)) {
            return found;
        }

        final int bitIndex = bitIndex(key, found.key);
        if (KeyAnalyzer.isValidBitIndex(bitIndex)) {
            final TrieEntry<K, V> added = new TrieEntry<>(key, null, bitIndex);
            addEntry(added, lengthInBits);
            incrementSize(); // must increment because remove will decrement
            final TrieEntry<K, V> ceil = nextEntry(added);
            removeEntry(added);
            modCount -= 2; // we didn't really modify it.
            return ceil;
        } else if (KeyAnalyzer.isNullBitKey(bitIndex)) {
            if (!root.isEmpty()) {
                return root;
            }
            return firstEntry();
        } else if (KeyAnalyzer.isEqualBitKey(bitIndex)) {
            return found;
        }

        // we should have exited above.
        throw new IllegalStateException("invalid lookup: " + key);
    }

    /**
     * Returns a key-value mapping associated with the greatest key
     * strictly less than the given key, or null if there is no such key.
     */
    TrieEntry<K,V> lowerEntry(final K key) {
        // Basically:
        // Follow the steps of adding an entry, but instead...
        //
        // - If we ever encounter a situation where we found an equal
        //   key, we return it's previousEntry immediately.
        //
        // - If we hit root (empty or not), return null.
        //
        // - If we have to add a new item, we temporarily add it,
        //   find the previousEntry to it, then remove the added item.
        //
        // These steps ensure that the returned value is always just before
        // the key or null (if there was nothing before it).

        // TODO: Cleanup so that we don't actually have to add/remove from the
        //       tree.  (We do it here because there are other well-defined
        //       functions to perform the search.)
        final int lengthInBits = lengthInBits(key);

        if (lengthInBits == 0) {
            return null; // there can never be anything before root.
        }

        final TrieEntry<K, V> found = getNearestEntryForKey(key, lengthInBits);
        if (compareKeys(key, found.key)) {
            return previousEntry(found);
        }

        final int bitIndex = bitIndex(key, found.key);
        if (KeyAnalyzer.isValidBitIndex(bitIndex)) {
            final TrieEntry<K, V> added = new TrieEntry<>(key, null, bitIndex);
            addEntry(added, lengthInBits);
            incrementSize(); // must increment because remove will decrement
            final TrieEntry<K, V> prior = previousEntry(added);
            removeEntry(added);
            modCount -= 2; // we didn't really modify it.
            return prior;
        } else if (KeyAnalyzer.isNullBitKey(bitIndex)) {
            return null;
        } else if (KeyAnalyzer.isEqualBitKey(bitIndex)) {
            return previousEntry(found);
        }

        // we should have exited above.
        throw new IllegalStateException("invalid lookup: " + key);
    }

    /**
     * Returns a key-value mapping associated with the greatest key
     * less than or equal to the given key, or null if there is no such key.
     */
    TrieEntry<K,V> floorEntry(final K key) {
        // TODO: Cleanup so that we don't actually have to add/remove from the
        //       tree.  (We do it here because there are other well-defined
        //       functions to perform the search.)
        final int lengthInBits = lengthInBits(key);

        if (lengthInBits == 0) {
            if (!root.isEmpty()) {
                return root;
            }
            return null;
        }

        final TrieEntry<K, V> found = getNearestEntryForKey(key, lengthInBits);
        if (compareKeys(key, found.key)) {
            return found;
        }

        final int bitIndex = bitIndex(key, found.key);
        if (KeyAnalyzer.isValidBitIndex(bitIndex)) {
            final TrieEntry<K, V> added = new TrieEntry<>(key, null, bitIndex);
            addEntry(added, lengthInBits);
            incrementSize(); // must increment because remove will decrement
            final TrieEntry<K, V> floor = previousEntry(added);
            removeEntry(added);
            modCount -= 2; // we didn't really modify it.
            return floor;
        } else if (KeyAnalyzer.isNullBitKey(bitIndex)) {
            if (!root.isEmpty()) {
                return root;
            }
            return null;
        } else if (KeyAnalyzer.isEqualBitKey(bitIndex)) {
            return found;
        }

        // we should have exited above.
        throw new IllegalStateException("invalid lookup: " + key);
    }

    /**
     * Finds the subtree that contains the prefix.
     *
     * This is very similar to getR but with the difference that
     * we stop the lookup if h.bitIndex > lengthInBits.
     */
    TrieEntry<K, V> subtree(final K prefix, final int offsetInBits, final int lengthInBits) {
        TrieEntry<K, V> current = root.left;
        TrieEntry<K, V> path = root;
        while(true) {
            if (current.bitIndex <= path.bitIndex || lengthInBits <= current.bitIndex) {
                break;
            }

            path = current;
            if (!isBitSet(prefix, offsetInBits + current.bitIndex, offsetInBits + lengthInBits)) {
                current = current.left;
            } else {
                current = current.right;
            }
        }

        // Make sure the entry is valid for a subtree.
        final TrieEntry<K, V> entry = current.isEmpty() ? path : current;

        // If entry is root, it can't be empty.
        if (entry.isEmpty()) {
            return null;
        }

        final int endIndexInBits = offsetInBits + lengthInBits;

        // if root && length of root is less than length of lookup,
        // there's nothing.
        // (this prevents returning the whole subtree if root has an empty
        //  string and we want to lookup things with "\0")
        if (entry == root && lengthInBits(entry.getKey()) < endIndexInBits) {
            return null;
        }

        // Found key's length-th bit differs from our key
        // which means it cannot be the prefix...
        if (isBitSet(prefix, endIndexInBits - 1, endIndexInBits)
                != isBitSet(entry.key, lengthInBits - 1, lengthInBits(entry.key))) {
            return null;
        }

        // ... or there are less than 'length' equal bits
        final int bitIndex = getKeyAnalyzer().bitIndex(prefix, offsetInBits, lengthInBits,
                                                       entry.key, 0, lengthInBits(entry.getKey()));

        if (bitIndex >= 0 && bitIndex < lengthInBits) {
            return null;
        }

        return entry;
    }

    /**
     * Returns the last entry the {@link Trie} is storing.
     *
     * <p>This is implemented by going always to the right until
     * we encounter a valid uplink. That uplink is the last key.
     */
    TrieEntry<K, V> lastEntry() {
        return followRight(root.left);
    }

    /**
     * Traverses down the right path until it finds an uplink.
     */
    TrieEntry<K, V> followRight(TrieEntry<K, V> node) {
        // if Trie is empty, no last entry.
        if (node.right == null) {
            return null;
        }

        // Go as far right as possible, until we encounter an uplink.
        while (node.right.bitIndex > node.bitIndex) {
            node = node.right;
        }

        return node.right;
    }

    /**
     * Returns the node lexicographically before the given node (or null if none).
     *
     * This follows four simple branches:
     *  - If the uplink that returned us was a right uplink:
     *      - If predecessor's left is a valid uplink from predecessor, return it.
     *      - Else, follow the right path from the predecessor's left.
     *  - If the uplink that returned us was a left uplink:
     *      - Loop back through parents until we encounter a node where
     *        node != node.parent.left.
     *          - If node.parent.left is uplink from node.parent:
     *              - If node.parent.left is not root, return it.
     *              - If it is root & root isEmpty, return null.
     *              - If it is root & root !isEmpty, return root.
     *          - If node.parent.left is not uplink from node.parent:
     *              - Follow right path for first right child from node.parent.left
     *
     * @param start  the start entry
     */
    TrieEntry<K, V> previousEntry(final TrieEntry<K, V> start) {
        if (start.predecessor == null) {
            throw new IllegalArgumentException("must have come from somewhere!");
        }

        if (start.predecessor.right == start) {
            if (isValidUplink(start.predecessor.left, start.predecessor)) {
                return start.predecessor.left;
            }
            return followRight(start.predecessor.left);
        }
        TrieEntry<K, V> node = start.predecessor;
        while (node.parent != null && node == node.parent.left) {
            node = node.parent;
        }

        if (node.parent == null) { // can be null if we're looking up root.
            return null;
        }

        if (isValidUplink(node.parent.left, node.parent)) {
            if (node.parent.left == root) {
                if (root.isEmpty()) {
                    return null;
                }
                return root;

            }
            return node.parent.left;
        }
        return followRight(node.parent.left);
    }

    /**
     * Returns the entry lexicographically after the given entry.
     * If the given entry is null, returns the first node.
     *
     * This will traverse only within the subtree.  If the given node
     * is not within the subtree, this will have undefined results.
     */
    TrieEntry<K, V> nextEntryInSubtree(final TrieEntry<K, V> node,
            final TrieEntry<K, V> parentOfSubtree) {
        if (node == null) {
            return firstEntry();
        }
        return nextEntryImpl(node.predecessor, node, parentOfSubtree);
    }

    /**
     * Returns true if 'next' is a valid uplink coming from 'from'.
     */
    static boolean isValidUplink(final TrieEntry<?, ?> next, final TrieEntry<?, ?> from) {
        return next != null && next.bitIndex <= from.bitIndex && !next.isEmpty();
    }

    /**
     * A {@link Reference} allows us to return something through a Method's
     * argument list. An alternative would be to an Array with a length of
     * one (1) but that leads to compiler warnings. Computationally and memory
     * wise there's no difference (except for the need to load the
     * {@link Reference} Class but that happens only once).
     */
    private static class Reference<E> {

        private E item;

        public void set(final E item) {
            this.item = item;
        }

        public E get() {
            return item;
        }
    }

    /**
     *  A {@link org.apache.commons.collections4.Trie} is a set of {@link TrieEntry} nodes.
     */
    protected static class TrieEntry<K,V> extends BasicEntry<K, V> {

        private static final long serialVersionUID = 4596023148184140013L;

        /** The index this entry is comparing. */
        protected int bitIndex;

        /** The parent of this entry. */
        protected TrieEntry<K,V> parent;

        /** The left child of this entry. */
        protected TrieEntry<K,V> left;

        /** The right child of this entry. */
        protected TrieEntry<K,V> right;

        /** The entry who uplinks to this entry. */
        protected TrieEntry<K,V> predecessor;

        public TrieEntry(final K key, final V value, final int bitIndex) {
            super(key, value);

            this.bitIndex = bitIndex;

            this.parent = null;
            this.left = this;
            this.right = null;
            this.predecessor = this;
        }

        /**
         * Whether or not the entry is storing a key.
         * Only the root can potentially be empty, all other
         * nodes must have a key.
         */
        public boolean isEmpty() {
            return key == null;
        }

        /**
         * Neither the left nor right child is a loopback.
         */
        public boolean isInternalNode() {
            return left != this && right != this;
        }

        /**
         * Either the left or right child is a loopback.
         */
        public boolean isExternalNode() {
            return !isInternalNode();
        }

        @Override
        public String toString() {
            final StringBuilder buffer = new StringBuilder();

            if (bitIndex == -1) {
                buffer.append("RootEntry(");
            } else {
                buffer.append("Entry(");
            }

            buffer.append("key=").append(getKey()).append(" [").append(bitIndex).append("], ");
            buffer.append("value=").append(getValue()).append(", ");
            //buffer.append("bitIndex=").append(bitIndex).append(", ");

            if (parent != null) {
                if (parent.bitIndex == -1) {
                    buffer.append("parent=").append("ROOT");
                } else {
                    buffer.append("parent=").append(parent.getKey()).append(" [").append(parent.bitIndex).append("]");
                }
            } else {
                buffer.append("parent=").append("null");
            }
            buffer.append(", ");

            if (left != null) {
                if (left.bitIndex == -1) {
                    buffer.append("left=").append("ROOT");
                } else {
                    buffer.append("left=").append(left.getKey()).append(" [").append(left.bitIndex).append("]");
                }
            } else {
                buffer.append("left=").append("null");
            }
            buffer.append(", ");

            if (right != null) {
                if (right.bitIndex == -1) {
                    buffer.append("right=").append("ROOT");
                } else {
                    buffer.append("right=").append(right.getKey()).append(" [").append(right.bitIndex).append("]");
                }
            } else {
                buffer.append("right=").append("null");
            }
            buffer.append(", ");

            if (predecessor != null) {
                if(predecessor.bitIndex == -1) {
                    buffer.append("predecessor=").append("ROOT");
                } else {
                    buffer.append("predecessor=").append(predecessor.getKey()).append(" [").
                           append(predecessor.bitIndex).append("]");
                }
            }

            buffer.append(")");
            return buffer.toString();
        }
    }


    /**
     * This is a entry set view of the {@link Trie} as returned by {@link Map#entrySet()}.
     */
    private class EntrySet extends AbstractSet<Map.Entry<K,V>> {

        @Override
        public Iterator<Map.Entry<K,V>> iterator() {
            return new EntryIterator();
        }

        @Override
        public boolean contains(final Object o) {
            if (!(o instanceof Map.Entry)) {
                return false;
            }

            final TrieEntry<K,V> candidate = getEntry(((Map.Entry<?, ?>)o).getKey());
            return candidate != null && candidate.equals(o);
        }

        @Override
        public boolean remove(final Object obj) {
            if (obj instanceof Map.Entry == false) {
                return false;
            }
            if (contains(obj) == false) {
                return false;
            }
            final Map.Entry<?, ?> entry = (Map.Entry<?, ?>) obj;
            AbstractPatriciaTrie.this.remove(entry.getKey());
            return true;
        }

        @Override
        public int size() {
            return AbstractPatriciaTrie.this.size();
        }

        @Override
        public void clear() {
            AbstractPatriciaTrie.this.clear();
        }

        /**
         * An {@link Iterator} that returns {@link Entry} Objects.
         */
        private class EntryIterator extends TrieIterator<Map.Entry<K,V>> {
            @Override
            public Map.Entry<K,V> next() {
                return nextEntry();
            }
        }
    }

    /**
     * This is a key set view of the {@link Trie} as returned by {@link Map#keySet()}.
     */
    private class KeySet extends AbstractSet<K> {

        @Override
        public Iterator<K> iterator() {
            return new KeyIterator();
        }

        @Override
        public int size() {
            return AbstractPatriciaTrie.this.size();
        }

        @Override
        public boolean contains(final Object o) {
            return containsKey(o);
        }

        @Override
        public boolean remove(final Object o) {
            final int size = size();
            AbstractPatriciaTrie.this.remove(o);
            return size != size();
        }

        @Override
        public void clear() {
            AbstractPatriciaTrie.this.clear();
        }

        /**
         * An {@link Iterator} that returns Key Objects.
         */
        private class KeyIterator extends TrieIterator<K> {
            @Override
            public K next() {
                return nextEntry().getKey();
            }
        }
    }

    /**
     * This is a value view of the {@link Trie} as returned by {@link Map#values()}.
     */
    private class Values extends AbstractCollection<V> {

        @Override
        public Iterator<V> iterator() {
            return new ValueIterator();
        }

        @Override
        public int size() {
            return AbstractPatriciaTrie.this.size();
        }

        @Override
        public boolean contains(final Object o) {
            return containsValue(o);
        }

        @Override
        public void clear() {
            AbstractPatriciaTrie.this.clear();
        }

        @Override
        public boolean remove(final Object o) {
            for (final Iterator<V> it = iterator(); it.hasNext(); ) {
                final V value = it.next();
                if (compare(value, o)) {
                    it.remove();
                    return true;
                }
            }
            return false;
        }

        /**
         * An {@link Iterator} that returns Value Objects.
         */
        private class ValueIterator extends TrieIterator<V> {
            @Override
            public V next() {
                return nextEntry().getValue();
            }
        }
    }

    /**
     * An iterator for the entries.
     */
    abstract class TrieIterator<E> implements Iterator<E> {

        /** For fast-fail. */
        protected int expectedModCount = AbstractPatriciaTrie.this.modCount;

        protected TrieEntry<K, V> next; // the next node to return
        protected TrieEntry<K, V> current; // the current entry we're on

        /**
         * Starts iteration from the root.
         */
        protected TrieIterator() {
            next = AbstractPatriciaTrie.this.nextEntry(null);
        }

        /**
         * Starts iteration at the given entry.
         */
        protected TrieIterator(final TrieEntry<K, V> firstEntry) {
            next = firstEntry;
        }

        /**
         * Returns the next {@link TrieEntry}.
         */
        protected TrieEntry<K,V> nextEntry() {
            if (expectedModCount != AbstractPatriciaTrie.this.modCount) {
                throw new ConcurrentModificationException();
            }

            final TrieEntry<K,V> e = next;
            if (e == null) {
                throw new NoSuchElementException();
            }

            next = findNext(e);
            current = e;
            return e;
        }

        /**
         * @see PatriciaTrie#nextEntry(TrieEntry)
         */
        protected TrieEntry<K, V> findNext(final TrieEntry<K, V> prior) {
            return AbstractPatriciaTrie.this.nextEntry(prior);
        }

        @Override
        public boolean hasNext() {
            return next != null;
        }

        @Override
        public void remove() {
            if (current == null) {
                throw new IllegalStateException();
            }

            if (expectedModCount != AbstractPatriciaTrie.this.modCount) {
                throw new ConcurrentModificationException();
            }

            final TrieEntry<K, V> node = current;
            current = null;
            AbstractPatriciaTrie.this.removeEntry(node);

            expectedModCount = AbstractPatriciaTrie.this.modCount;
        }
    }

    /**
     * An {@link OrderedMapIterator} for a {@link Trie}.
     */
    private class TrieMapIterator extends TrieIterator<K> implements OrderedMapIterator<K, V> {

        protected TrieEntry<K, V> previous; // the previous node to return

        @Override
        public K next() {
            return nextEntry().getKey();
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
        public V setValue(final V value) {
            if (current == null) {
                throw new IllegalStateException();
            }
            return current.setValue(value);
        }

        @Override
        public boolean hasPrevious() {
            return previous != null;
        }

        @Override
        public K previous() {
            return previousEntry().getKey();
        }

        @Override
        protected TrieEntry<K, V> nextEntry() {
            final TrieEntry<K, V> nextEntry = super.nextEntry();
            previous = nextEntry;
            return nextEntry;
        }

        protected TrieEntry<K,V> previousEntry() {
            if (expectedModCount != AbstractPatriciaTrie.this.modCount) {
                throw new ConcurrentModificationException();
            }

            final TrieEntry<K,V> e = previous;
            if (e == null) {
                throw new NoSuchElementException();
            }

            previous = AbstractPatriciaTrie.this.previousEntry(e);
            next = current;
            current = e;
            return current;
        }

    }

    /**
     * A range view of the {@link Trie}.
     */
    private abstract class RangeMap extends AbstractMap<K, V>
            implements SortedMap<K, V> {

        /** The {@link #entrySet()} view. */
        private transient volatile Set<Map.Entry<K, V>> entrySet;

        /**
         * Creates and returns an {@link #entrySet()} view of the {@link RangeMap}.
         */
        protected abstract Set<Map.Entry<K, V>> createEntrySet();

        /**
         * Returns the FROM Key.
         */
        protected abstract K getFromKey();

        /**
         * Whether or not the {@link #getFromKey()} is in the range.
         */
        protected abstract boolean isFromInclusive();

        /**
         * Returns the TO Key.
         */
        protected abstract K getToKey();

        /**
         * Whether or not the {@link #getToKey()} is in the range.
         */
        protected abstract boolean isToInclusive();

        @Override
        public Comparator<? super K> comparator() {
            return AbstractPatriciaTrie.this.comparator();
        }

        @Override
        public boolean containsKey(final Object key) {
            if (!inRange(castKey(key))) {
                return false;
            }

            return AbstractPatriciaTrie.this.containsKey(key);
        }

        @Override
        public V remove(final Object key) {
            if (!inRange(castKey(key))) {
                return null;
            }

            return AbstractPatriciaTrie.this.remove(key);
        }

        @Override
        public V get(final Object key) {
            if (!inRange(castKey(key))) {
                return null;
            }

            return AbstractPatriciaTrie.this.get(key);
        }

        @Override
        public V put(final K key, final V value) {
            if (!inRange(key)) {
                throw new IllegalArgumentException("Key is out of range: " + key);
            }
            return AbstractPatriciaTrie.this.put(key, value);
        }

        @Override
        public Set<Map.Entry<K, V>> entrySet() {
            if (entrySet == null) {
                entrySet = createEntrySet();
            }
            return entrySet;
        }

        @Override
        public SortedMap<K, V> subMap(final K fromKey, final K toKey) {
            if (!inRange2(fromKey)) {
                throw new IllegalArgumentException("FromKey is out of range: " + fromKey);
            }

            if (!inRange2(toKey)) {
                throw new IllegalArgumentException("ToKey is out of range: " + toKey);
            }

            return createRangeMap(fromKey, isFromInclusive(), toKey, isToInclusive());
        }

        @Override
        public SortedMap<K, V> headMap(final K toKey) {
            if (!inRange2(toKey)) {
                throw new IllegalArgumentException("ToKey is out of range: " + toKey);
            }
            return createRangeMap(getFromKey(), isFromInclusive(), toKey, isToInclusive());
        }

        @Override
        public SortedMap<K, V> tailMap(final K fromKey) {
            if (!inRange2(fromKey)) {
                throw new IllegalArgumentException("FromKey is out of range: " + fromKey);
            }
            return createRangeMap(fromKey, isFromInclusive(), getToKey(), isToInclusive());
        }

        /**
         * Returns true if the provided key is greater than TO and less than FROM.
         */
        protected boolean inRange(final K key) {
            final K fromKey = getFromKey();
            final K toKey = getToKey();

            return (fromKey == null || inFromRange(key, false)) && (toKey == null || inToRange(key, false));
        }

        /**
         * This form allows the high endpoint (as well as all legit keys).
         */
        protected boolean inRange2(final K key) {
            final K fromKey = getFromKey();
            final K toKey = getToKey();

            return (fromKey == null || inFromRange(key, false)) && (toKey == null || inToRange(key, true));
        }

        /**
         * Returns true if the provided key is in the FROM range of the {@link RangeMap}.
         */
        protected boolean inFromRange(final K key, final boolean forceInclusive) {
            final K fromKey = getFromKey();
            final boolean fromInclusive = isFromInclusive();

            final int ret = getKeyAnalyzer().compare(key, fromKey);
            if (fromInclusive || forceInclusive) {
                return ret >= 0;
            }
            return ret > 0;
        }

        /**
         * Returns true if the provided key is in the TO range of the {@link RangeMap}.
         */
        protected boolean inToRange(final K key, final boolean forceInclusive) {
            final K toKey = getToKey();
            final boolean toInclusive = isToInclusive();

            final int ret = getKeyAnalyzer().compare(key, toKey);
            if (toInclusive || forceInclusive) {
                return ret <= 0;
            }
            return ret < 0;
        }

        /**
         * Creates and returns a sub-range view of the current {@link RangeMap}.
         */
        protected abstract SortedMap<K, V> createRangeMap(K fromKey, boolean fromInclusive,
                                                          K toKey, boolean toInclusive);
    }

   /**
    * A {@link RangeMap} that deals with {@link Entry}s.
    */
   private class RangeEntryMap extends RangeMap {

       /** The key to start from, null if the beginning. */
       private final K fromKey;

       /** The key to end at, null if till the end. */
       private final K toKey;

       /** Whether or not the 'from' is inclusive. */
       private final boolean fromInclusive;

       /** Whether or not the 'to' is inclusive. */
       private final boolean toInclusive;

       /**
        * Creates a {@link RangeEntryMap} with the fromKey included and
        * the toKey excluded from the range.
        */
       protected RangeEntryMap(final K fromKey, final K toKey) {
           this(fromKey, true, toKey, false);
       }

       /**
        * Creates a {@link RangeEntryMap}.
        */
       protected RangeEntryMap(final K fromKey, final boolean fromInclusive,
                               final K toKey, final boolean toInclusive) {

           if (fromKey == null && toKey == null) {
               throw new IllegalArgumentException("must have a from or to!");
           }

           if (fromKey != null && toKey != null && getKeyAnalyzer().compare(fromKey, toKey) > 0) {
               throw new IllegalArgumentException("fromKey > toKey");
           }

           this.fromKey = fromKey;
           this.fromInclusive = fromInclusive;
           this.toKey = toKey;
           this.toInclusive = toInclusive;
       }

       @Override
    public K firstKey() {
           Map.Entry<K,V> e = null;
           if (fromKey == null) {
               e = firstEntry();
           } else {
               if (fromInclusive) {
                   e = ceilingEntry(fromKey);
               } else {
                   e = higherEntry(fromKey);
               }
           }

           final K first = e != null ? e.getKey() : null;
           if (e == null || toKey != null && !inToRange(first, false)) {
               throw new NoSuchElementException();
           }
           return first;
       }

       @Override
    public K lastKey() {
           Map.Entry<K,V> e;
           if (toKey == null) {
               e = lastEntry();
           } else {
               if (toInclusive) {
                   e = floorEntry(toKey);
               } else {
                   e = lowerEntry(toKey);
               }
           }

           final K last = e != null ? e.getKey() : null;
           if (e == null || fromKey != null && !inFromRange(last, false)) {
               throw new NoSuchElementException();
           }
           return last;
       }

       @Override
       protected Set<Entry<K, V>> createEntrySet() {
           return new RangeEntrySet(this);
       }

       @Override
       public K getFromKey() {
           return fromKey;
       }

       @Override
       public K getToKey() {
           return toKey;
       }

       @Override
       public boolean isFromInclusive() {
           return fromInclusive;
       }

       @Override
       public boolean isToInclusive() {
           return toInclusive;
       }

       @Override
       protected SortedMap<K, V> createRangeMap(final K fromKey, final boolean fromInclusive,
                                                final K toKey, final boolean toInclusive) {
           return new RangeEntryMap(fromKey, fromInclusive, toKey, toInclusive);
       }
   }

    /**
     * A {@link Set} view of a {@link RangeMap}.
     */
    private class RangeEntrySet extends AbstractSet<Map.Entry<K, V>> {

        private final RangeMap delegate;

        private transient int size = -1;

        private transient int expectedModCount;

        /**
         * Creates a {@link RangeEntrySet}.
         */
        public RangeEntrySet(final RangeMap delegate) {
            if (delegate == null) {
                throw new NullPointerException("delegate");
            }

            this.delegate = delegate;
        }

        @Override
        public Iterator<Map.Entry<K, V>> iterator() {
            final K fromKey = delegate.getFromKey();
            final K toKey = delegate.getToKey();

            TrieEntry<K, V> first = null;
            if (fromKey == null) {
                first = firstEntry();
            } else {
                first = ceilingEntry(fromKey);
            }

            TrieEntry<K, V> last = null;
            if (toKey != null) {
                last = ceilingEntry(toKey);
            }

            return new EntryIterator(first, last);
        }

        @Override
        public int size() {
            if (size == -1 || expectedModCount != AbstractPatriciaTrie.this.modCount) {
                size = 0;

                for (final Iterator<?> it = iterator(); it.hasNext(); it.next()) {
                    ++size;
                }

                expectedModCount = AbstractPatriciaTrie.this.modCount;
            }
            return size;
        }

        @Override
        public boolean isEmpty() {
            return !iterator().hasNext();
        }

        @SuppressWarnings("unchecked")
        @Override
        public boolean contains(final Object o) {
            if (!(o instanceof Map.Entry)) {
                return false;
            }

            final Map.Entry<K, V> entry = (Map.Entry<K, V>) o;
            final K key = entry.getKey();
            if (!delegate.inRange(key)) {
                return false;
            }

            final TrieEntry<K, V> node = getEntry(key);
            return node != null && compare(node.getValue(), entry.getValue());
        }

        @SuppressWarnings("unchecked")
        @Override
        public boolean remove(final Object o) {
            if (!(o instanceof Map.Entry)) {
                return false;
            }

            final Map.Entry<K, V> entry = (Map.Entry<K, V>) o;
            final K key = entry.getKey();
            if (!delegate.inRange(key)) {
                return false;
            }

            final TrieEntry<K, V> node = getEntry(key);
            if (node != null && compare(node.getValue(), entry.getValue())) {
                removeEntry(node);
                return true;
            }
            return false;
        }

        /**
         * An {@link Iterator} for {@link RangeEntrySet}s.
         */
        private final class EntryIterator extends TrieIterator<Map.Entry<K,V>> {

            private final K excludedKey;

            /**
             * Creates a {@link EntryIterator}.
             */
            private EntryIterator(final TrieEntry<K,V> first, final TrieEntry<K,V> last) {
                super(first);
                this.excludedKey = last != null ? last.getKey() : null;
            }

            @Override
            public boolean hasNext() {
                return next != null && !compare(next.key, excludedKey);
            }

            @Override
            public Map.Entry<K,V> next() {
                if (next == null || compare(next.key, excludedKey)) {
                    throw new NoSuchElementException();
                }
                return nextEntry();
            }
        }
    }

    /**
     * A submap used for prefix views over the {@link Trie}.
     */
    private class PrefixRangeMap extends RangeMap {

        private final K prefix;

        private final int offsetInBits;

        private final int lengthInBits;

        private K fromKey = null;

        private K toKey = null;

        private transient int expectedModCount = 0;

        private int size = -1;

        /**
         * Creates a {@link PrefixRangeMap}.
         */
        private PrefixRangeMap(final K prefix, final int offsetInBits, final int lengthInBits) {
            this.prefix = prefix;
            this.offsetInBits = offsetInBits;
            this.lengthInBits = lengthInBits;
        }

        /**
         * This method does two things. It determines the FROM
         * and TO range of the {@link PrefixRangeMap} and the number
         * of elements in the range. This method must be called every
         * time the {@link Trie} has changed.
         */
        private int fixup() {
            // The trie has changed since we last found our toKey / fromKey
            if (size == - 1 || AbstractPatriciaTrie.this.modCount != expectedModCount) {
                final Iterator<Map.Entry<K, V>> it = super.entrySet().iterator();
                size = 0;

                Map.Entry<K, V> entry = null;
                if (it.hasNext()) {
                    entry = it.next();
                    size = 1;
                }

                fromKey = entry == null ? null : entry.getKey();
                if (fromKey != null) {
                    final TrieEntry<K, V> prior = previousEntry((TrieEntry<K, V>)entry);
                    fromKey = prior == null ? null : prior.getKey();
                }

                toKey = fromKey;

                while (it.hasNext()) {
                    ++size;
                    entry = it.next();
                }

                toKey = entry == null ? null : entry.getKey();

                if (toKey != null) {
                    entry = nextEntry((TrieEntry<K, V>)entry);
                    toKey = entry == null ? null : entry.getKey();
                }

                expectedModCount = AbstractPatriciaTrie.this.modCount;
            }

            return size;
        }

        @Override
        public K firstKey() {
            fixup();

            Map.Entry<K,V> e = null;
            if (fromKey == null) {
                e = firstEntry();
            } else {
                e = higherEntry(fromKey);
            }

            final K first = e != null ? e.getKey() : null;
            if (e == null || !getKeyAnalyzer().isPrefix(prefix, offsetInBits, lengthInBits, first)) {
                throw new NoSuchElementException();
            }

            return first;
        }

        @Override
        public K lastKey() {
            fixup();

            Map.Entry<K,V> e = null;
            if (toKey == null) {
                e = lastEntry();
            } else {
                e = lowerEntry(toKey);
            }

            final K last = e != null ? e.getKey() : null;
            if (e == null || !getKeyAnalyzer().isPrefix(prefix, offsetInBits, lengthInBits, last)) {
                throw new NoSuchElementException();
            }

            return last;
        }

        /**
         * Returns true if this {@link PrefixRangeMap}'s key is a prefix of the provided key.
         */
        @Override
        protected boolean inRange(final K key) {
            return getKeyAnalyzer().isPrefix(prefix, offsetInBits, lengthInBits, key);
        }

        /**
         * Same as {@link #inRange(Object)}.
         */
        @Override
        protected boolean inRange2(final K key) {
            return inRange(key);
        }

        /**
         * Returns true if the provided Key is in the FROM range of the {@link PrefixRangeMap}.
         */
        @Override
        protected boolean inFromRange(final K key, final boolean forceInclusive) {
            return getKeyAnalyzer().isPrefix(prefix, offsetInBits, lengthInBits, key);
        }

        /**
         * Returns true if the provided Key is in the TO range of the {@link PrefixRangeMap}.
         */
        @Override
        protected boolean inToRange(final K key, final boolean forceInclusive) {
            return getKeyAnalyzer().isPrefix(prefix, offsetInBits, lengthInBits, key);
        }

        @Override
        protected Set<Map.Entry<K, V>> createEntrySet() {
            return new PrefixRangeEntrySet(this);
        }

        @Override
        public K getFromKey() {
            return fromKey;
        }

        @Override
        public K getToKey() {
            return toKey;
        }

        @Override
        public boolean isFromInclusive() {
            return false;
        }

        @Override
        public boolean isToInclusive() {
            return false;
        }

        @Override
        protected SortedMap<K, V> createRangeMap(final K fromKey, final boolean fromInclusive,
                                                 final K toKey, final boolean toInclusive) {
            return new RangeEntryMap(fromKey, fromInclusive, toKey, toInclusive);
        }

        @Override
        public void clear() {
            final Iterator<Map.Entry<K, V>> it = AbstractPatriciaTrie.this.entrySet().iterator();
            final Set<K> currentKeys = keySet();
            while (it.hasNext()) {
                if (currentKeys.contains(it.next().getKey())) {
                    it.remove();
                }
            }
        }
    }

    /**
     * A prefix {@link RangeEntrySet} view of the {@link Trie}.
     */
    private final class PrefixRangeEntrySet extends RangeEntrySet {

        private final PrefixRangeMap delegate;

        private TrieEntry<K, V> prefixStart;

        private int expectedModCount = 0;

        /**
         * Creates a {@link PrefixRangeEntrySet}.
         */
        public PrefixRangeEntrySet(final PrefixRangeMap delegate) {
            super(delegate);
            this.delegate = delegate;
        }

        @Override
        public int size() {
            return delegate.fixup();
        }

        @Override
        public Iterator<Map.Entry<K,V>> iterator() {
            if (AbstractPatriciaTrie.this.modCount != expectedModCount) {
                prefixStart = subtree(delegate.prefix, delegate.offsetInBits, delegate.lengthInBits);
                expectedModCount = AbstractPatriciaTrie.this.modCount;
            }

            if (prefixStart == null) {
                final Set<Map.Entry<K,V>> empty = Collections.emptySet();
                return empty.iterator();
            } else if (delegate.lengthInBits > prefixStart.bitIndex) {
                return new SingletonIterator(prefixStart);
            } else {
                return new EntryIterator(prefixStart, delegate.prefix, delegate.offsetInBits, delegate.lengthInBits);
            }
        }

        /**
         * An {@link Iterator} that holds a single {@link TrieEntry}.
         */
        private final class SingletonIterator implements Iterator<Map.Entry<K, V>> {

            private final TrieEntry<K, V> entry;

            private int hit = 0;

            public SingletonIterator(final TrieEntry<K, V> entry) {
                this.entry = entry;
            }

            @Override
            public boolean hasNext() {
                return hit == 0;
            }

            @Override
            public Map.Entry<K, V> next() {
                if (hit != 0) {
                    throw new NoSuchElementException();
                }

                ++hit;
                return entry;
            }

            @Override
            public void remove() {
                if (hit != 1) {
                    throw new IllegalStateException();
                }

                ++hit;
                AbstractPatriciaTrie.this.removeEntry(entry);
            }
        }

        /**
         * An {@link Iterator} for iterating over a prefix search.
         */
        private final class EntryIterator extends TrieIterator<Map.Entry<K, V>> {

            // values to reset the subtree if we remove it.
            private final K prefix;
            private final int offset;
            private final int lengthInBits;
            private boolean lastOne;

            private TrieEntry<K, V> subtree; // the subtree to search within

            /**
             * Starts iteration at the given entry & search only
             * within the given subtree.
             */
            EntryIterator(final TrieEntry<K, V> startScan, final K prefix,
                    final int offset, final int lengthInBits) {
                subtree = startScan;
                next = AbstractPatriciaTrie.this.followLeft(startScan);
                this.prefix = prefix;
                this.offset = offset;
                this.lengthInBits = lengthInBits;
            }

            @Override
            public Map.Entry<K,V> next() {
                final Map.Entry<K, V> entry = nextEntry();
                if (lastOne) {
                    next = null;
                }
                return entry;
            }

            @Override
            protected TrieEntry<K, V> findNext(final TrieEntry<K, V> prior) {
                return AbstractPatriciaTrie.this.nextEntryInSubtree(prior, subtree);
            }

            @Override
            public void remove() {
                // If the current entry we're removing is the subtree
                // then we need to find a new subtree parent.
                boolean needsFixing = false;
                final int bitIdx = subtree.bitIndex;
                if (current == subtree) {
                    needsFixing = true;
                }

                super.remove();

                // If the subtree changed its bitIndex or we
                // removed the old subtree, get a new one.
                if (bitIdx != subtree.bitIndex || needsFixing) {
                    subtree = subtree(prefix, offset, lengthInBits);
                }

                // If the subtree's bitIndex is less than the
                // length of our prefix, it's the last item
                // in the prefix tree.
                if (lengthInBits >= subtree.bitIndex) {
                    lastOne = true;
                }
            }
        }
    }

    //-----------------------------------------------------------------------

    /**
     * Reads the content of the stream.
     */
    @SuppressWarnings("unchecked") // This will fail at runtime if the stream is incorrect
    private void readObject(final ObjectInputStream stream) throws IOException, ClassNotFoundException{
        stream.defaultReadObject();
        root = new TrieEntry<>(null, null, -1);
        final int size = stream.readInt();
        for(int i = 0; i < size; i++){
            final K k = (K) stream.readObject();
            final V v = (V) stream.readObject();
            put(k, v);
        }
    }

    /**
     * Writes the content to the stream for serialization.
     */
    private void writeObject(final ObjectOutputStream stream) throws IOException{
        stream.defaultWriteObject();
        stream.writeInt(this.size());
        for (final Entry<K, V> entry : entrySet()) {
            stream.writeObject(entry.getKey());
            stream.writeObject(entry.getValue());
        }
    }

}
