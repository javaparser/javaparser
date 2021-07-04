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
package org.apache.commons.math3.util;

/**
 * Generic pair.
 * <br/>
 * Although the instances of this class are immutable, it is impossible
 * to ensure that the references passed to the constructor will not be
 * modified by the caller.
 *
 * @param <K> Key type.
 * @param <V> Value type.
 *
 * @since 3.0
 */
public class Pair<K, V> {
    /** Key. */
    private final K key;
    /** Value. */
    private final V value;

    /**
     * Create an entry representing a mapping from the specified key to the
     * specified value.
     *
     * @param k Key (first element of the pair).
     * @param v Value (second element of the pair).
     */
    public Pair(K k, V v) {
        key = k;
        value = v;
    }

    /**
     * Create an entry representing the same mapping as the specified entry.
     *
     * @param entry Entry to copy.
     */
    public Pair(Pair<? extends K, ? extends V> entry) {
        this(entry.getKey(), entry.getValue());
    }

    /**
     * Get the key.
     *
     * @return the key (first element of the pair).
     */
    public K getKey() {
        return key;
    }

    /**
     * Get the value.
     *
     * @return the value (second element of the pair).
     */
    public V getValue() {
        return value;
    }

    /**
     * Get the first element of the pair.
     *
     * @return the first element of the pair.
     * @since 3.1
     */
    public K getFirst() {
        return key;
    }

    /**
     * Get the second element of the pair.
     *
     * @return the second element of the pair.
     * @since 3.1
     */
    public V getSecond() {
        return value;
    }

    /**
     * Compare the specified object with this entry for equality.
     *
     * @param o Object.
     * @return {@code true} if the given object is also a map entry and
     * the two entries represent the same mapping.
     */
    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (!(o instanceof Pair)) {
            return false;
        } else {
            Pair<?, ?> oP = (Pair<?, ?>) o;
            return (key == null ?
                    oP.key == null :
                    key.equals(oP.key)) &&
                (value == null ?
                 oP.value == null :
                 value.equals(oP.value));
        }
    }

    /**
     * Compute a hash code.
     *
     * @return the hash code value.
     */
    @Override
    public int hashCode() {
        int result = key == null ? 0 : key.hashCode();

        final int h = value == null ? 0 : value.hashCode();
        result = 37 * result + h ^ (h >>> 16);

        return result;
    }

    /** {@inheritDoc} */
    @Override
    public String toString() {
        return "[" + getKey() + ", " + getValue() + "]";
    }

    /**
     * Convenience factory method that calls the
     * {@link #Pair(Object, Object) constructor}.
     *
     * @param <K> the key type
     * @param <V> the value type
     * @param k First element of the pair.
     * @param v Second element of the pair.
     * @return a new {@code Pair} containing {@code k} and {@code v}.
     * @since 3.3
     */
    public static <K, V> Pair<K, V> create(K k, V v) {
        return new Pair<K, V>(k, v);
    }
}
