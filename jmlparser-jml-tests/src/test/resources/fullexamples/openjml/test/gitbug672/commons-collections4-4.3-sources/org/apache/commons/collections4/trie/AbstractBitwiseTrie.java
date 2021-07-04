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

import java.io.Serializable;
import java.util.AbstractMap;
import java.util.Map;
import java.util.Map.Entry;

import org.apache.commons.collections4.Trie;

/**
 * This class provides some basic {@link Trie} functionality and
 * utility methods for actual bitwise {@link Trie} implementations.
 *
 * @param <K> the type of the keys in this map
 * @param <V> the type of the values in this map
 * @since 4.0
 */
public abstract class AbstractBitwiseTrie<K, V> extends AbstractMap<K, V>
        implements Trie<K, V>, Serializable {

    private static final long serialVersionUID = 5826987063535505652L;

    /**
     * The {@link KeyAnalyzer} that's being used to build the PATRICIA {@link Trie}.
     */
    private final KeyAnalyzer<? super K> keyAnalyzer;

    /**
     * Constructs a new {@link Trie} using the given {@link KeyAnalyzer}.
     *
     * @param keyAnalyzer  the {@link KeyAnalyzer} to use
     */
    protected AbstractBitwiseTrie(final KeyAnalyzer<? super K> keyAnalyzer) {
        if (keyAnalyzer == null) {
            throw new NullPointerException("keyAnalyzer");
        }

        this.keyAnalyzer = keyAnalyzer;
    }

    /**
     * Returns the {@link KeyAnalyzer} that constructed the {@link Trie}.
     * @return the {@link KeyAnalyzer} used by this {@link Trie}
     */
    protected KeyAnalyzer<? super K> getKeyAnalyzer() {
        return keyAnalyzer;
    }

    @Override
    public String toString() {
        final StringBuilder buffer = new StringBuilder();
        buffer.append("Trie[").append(size()).append("]={\n");
        for (final Map.Entry<K, V> entry : entrySet()) {
            buffer.append("  ").append(entry).append("\n");
        }
        buffer.append("}\n");
        return buffer.toString();
    }

    /**
     * A utility method to cast keys. It actually doesn't cast anything. It's just fooling the compiler!
     */
    @SuppressWarnings("unchecked")
    final K castKey(final Object key) {
        return (K) key;
    }

    /**
     * Returns the length of the given key in bits
     *
     * @see KeyAnalyzer#lengthInBits(Object)
     */
    final int lengthInBits(final K key) {
        if (key == null) {
            return 0;
        }

        return keyAnalyzer.lengthInBits(key);
    }

    /**
     * Returns the number of bits per element in the key
     *
     * @see KeyAnalyzer#bitsPerElement()
     */
    final int bitsPerElement() {
        return keyAnalyzer.bitsPerElement();
    }

    /**
     * Returns whether or not the given bit on the key is set or false if the key is null.
     *
     * @see KeyAnalyzer#isBitSet(Object, int, int)
     */
    final boolean isBitSet(final K key, final int bitIndex, final int lengthInBits) {
        if (key == null) { // root's might be null!
            return false;
        }
        return keyAnalyzer.isBitSet(key, bitIndex, lengthInBits);
    }

    /**
     * Utility method for calling {@link KeyAnalyzer#bitIndex(Object, int, int, Object, int, int)}.
     */
    final int bitIndex(final K key, final K foundKey) {
        return keyAnalyzer.bitIndex(key, 0, lengthInBits(key), foundKey, 0, lengthInBits(foundKey));
    }

    /**
     * An utility method for calling {@link KeyAnalyzer#compare(Object, Object)}
     */
    final boolean compareKeys(final K key, final K other) {
        if (key == null) {
            return other == null;
        } else if (other == null) {
            return false;
        }

        return keyAnalyzer.compare(key, other) == 0;
    }

    /**
     * Returns true if both values are either null or equal.
     */
    static boolean compare(final Object a, final Object b) {
        return a == null ? b == null : a.equals(b);
    }

    /**
     * A basic implementation of {@link Entry}.
     */
    abstract static class BasicEntry<K, V> implements Map.Entry<K, V>, Serializable {

        private static final long serialVersionUID = -944364551314110330L;

        protected K key;

        protected V value;

        public BasicEntry(final K key) {
            this.key = key;
        }

        public BasicEntry(final K key, final V value) {
            this.key = key;
            this.value = value;
        }

        /**
         * Replaces the current key and value with the provided key &amp; value.
         */
        public V setKeyValue(final K key, final V value) {
            this.key = key;
            return setValue(value);
        }

        @Override
        public K getKey() {
            return key;
        }

        @Override
        public V getValue() {
            return value;
        }

        @Override
        public V setValue(final V value) {
            final V previous = this.value;
            this.value = value;
            return previous;
        }

        @Override
        public int hashCode() {
            return (getKey() == null ? 0 : getKey().hashCode()) ^
                   (getValue() == null ? 0 : getValue().hashCode());
        }

        @Override
        public boolean equals(final Object o) {
            if (o == this) {
                return true;
            } else if (!(o instanceof Map.Entry)) {
                return false;
            }

            final Map.Entry<?, ?> other = (Map.Entry<?, ?>)o;
            if (compare(key, other.getKey())
                    && compare(value, other.getValue())) {
                return true;
            }
            return false;
        }

        @Override
        public String toString() {
            return key + "=" + value;
        }
    }
}
