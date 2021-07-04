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
package org.apache.commons.collections4;

import org.apache.commons.collections4.trie.UnmodifiableTrie;

/**
 * A collection of {@link Trie} utilities.
 *
 * @since 4.0
 */
public class TrieUtils {

    /**
     * {@link TrieUtils} should not normally be instantiated.
     */
    private TrieUtils() {}

    /**
     * Returns an unmodifiable instance of a {@link Trie}
     *
     * @param <K>  the key type
     * @param <V>  the value type
     * @param trie  the trie to make unmodifiable, must not be null
     * @return an unmodifiable trie backed by the given trie
     * @throws NullPointerException if trie is null
     *
     * @see java.util.Collections#unmodifiableMap(java.util.Map)
     */
    public static <K, V> Trie<K, V> unmodifiableTrie(final Trie<K, ? extends V> trie) {
        return UnmodifiableTrie.unmodifiableTrie(trie);
    }

}
