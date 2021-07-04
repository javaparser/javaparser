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
import java.util.Comparator;

/**
 * Defines the interface to analyze {@link org.apache.commons.collections4.Trie Trie} keys on a bit level.
 * {@link KeyAnalyzer}'s methods return the length of the key in bits, whether or not a bit is set,
 * and bits per element in the key.
 * <p>
 * Additionally, a method determines if a key is a prefix of another
 * key and returns the bit index where one key is different from another
 * key (if the key and found key are equal than the return value is
 * {@link #EQUAL_BIT_KEY}).
 *
 * @param <K> the type of objects that may be compared by this analyzer
 * @since 4.0
 */
public abstract class KeyAnalyzer<K> implements Comparator<K>, Serializable {

    /** Serialization version */
    private static final long serialVersionUID = -20497563720380683L;

    /**
     * Returned by {@link #bitIndex(Object, int, int, Object, int, int)}
     * if key's bits are all 0.
     */
    public static final int NULL_BIT_KEY = -1;

    /**
     * Returned by {@link #bitIndex(Object, int, int, Object, int, int)} if key and found key are equal.
     * This is a very very specific case and shouldn't happen on a regular basis.
     */
    public static final int EQUAL_BIT_KEY = -2;

    public static final int OUT_OF_BOUNDS_BIT_KEY = -3;

    /**
     * Returns true if bitIndex is a {@link KeyAnalyzer#OUT_OF_BOUNDS_BIT_KEY}.
     */
    static boolean isOutOfBoundsIndex(final int bitIndex) {
        return bitIndex == OUT_OF_BOUNDS_BIT_KEY;
    }

    /**
     * Returns true if bitIndex is a {@link KeyAnalyzer#EQUAL_BIT_KEY}.
     */
    static boolean isEqualBitKey(final int bitIndex) {
        return bitIndex == EQUAL_BIT_KEY;
    }

    /**
     * Returns true if bitIndex is a {@link KeyAnalyzer#NULL_BIT_KEY}.
     */
    static boolean isNullBitKey(final int bitIndex) {
        return bitIndex == NULL_BIT_KEY;
    }

    /**
     * Returns true if the given bitIndex is valid.
     * Indices are considered valid if they're between 0 and {@link Integer#MAX_VALUE}
     */
    static boolean isValidBitIndex(final int bitIndex) {
        return bitIndex >= 0;
    }

    /**
     * Returns the number of bits per element in the key.
     * This is only useful for variable-length keys, such as Strings.
     *
     * @return the number of bits per element
     */
    public abstract int bitsPerElement();

    /**
     * Returns the length of the Key in bits.
     *
     * @param key  the key
     * @return the bit length of the key
     */
    public abstract int lengthInBits(K key);

    /**
     * Returns whether or not a bit is set.
     *
     * @param key  the key to check, may not be null
     * @param bitIndex  the bit index to check
     * @param lengthInBits  the maximum key length in bits to check
     * @return {@code true} if the bit is set in the given key and
     *   {@code bitIndex} &lt; {@code lengthInBits}, {@code false} otherwise.
     */
    public abstract boolean isBitSet(K key, int bitIndex, int lengthInBits);

    /**
     * Returns the n-th different bit between key and other. This starts the comparison in
     * key at 'offsetInBits' and goes for 'lengthInBits' bits, and compares to the other key starting
     * at 'otherOffsetInBits' and going for 'otherLengthInBits' bits.
     *
     * @param key  the key to use
     * @param offsetInBits  the bit offset in the key
     * @param lengthInBits  the maximum key length in bits to use
     * @param other  the other key to use
     * @param otherOffsetInBits  the bit offset in the other key
     * @param otherLengthInBits  the maximum key length in bits for the other key
     * @return the bit index where the key and other first differ
     */
    public abstract int bitIndex(K key, int offsetInBits, int lengthInBits,
                                 K other, int otherOffsetInBits, int otherLengthInBits);

    /**
     * Determines whether or not the given prefix (from offset to length) is a prefix of the given key.
     *
     * @param prefix  the prefix to check
     * @param offsetInBits  the bit offset in the key
     * @param lengthInBits  the maximum key length in bits to use
     * @param key  the key to check
     * @return {@code true} if this is a valid prefix for the given key
     */
    public abstract boolean isPrefix(K prefix, int offsetInBits, int lengthInBits, K key);

    @Override
    @SuppressWarnings("unchecked")
    public int compare(final K o1, final K o2) {
        if (o1 == null) {
            return o2 == null ? 0 : -1;
        } else if (o2 == null) {
            return 1;
        }

        return ((Comparable<K>) o1).compareTo(o2);
    }

}
