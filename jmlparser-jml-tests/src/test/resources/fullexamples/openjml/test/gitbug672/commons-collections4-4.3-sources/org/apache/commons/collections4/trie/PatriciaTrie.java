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

import java.util.Map;

import org.apache.commons.collections4.trie.analyzer.StringKeyAnalyzer;

/**
 * Implementation of a PATRICIA Trie (Practical Algorithm to Retrieve Information
 * Coded in Alphanumeric).
 * <p>
 * A PATRICIA {@link org.apache.commons.collections4.Trie} is a compressed
 * {@link org.apache.commons.collections4.Trie}. Instead of storing
 * all data at the edges of the {@link org.apache.commons.collections4.Trie}
 * (and having empty internal nodes), PATRICIA stores data in every node.
 * This allows for very efficient traversal, insert, delete, predecessor,
 * successor, prefix, range, and {@link #select(Object)}
 * operations. All operations are performed at worst in O(K) time, where K
 * is the number of bits in the largest item in the tree. In practice,
 * operations actually take O(A(K)) time, where A(K) is the average number of
 * bits of all items in the tree.
 * <p>
 * Most importantly, PATRICIA requires very few comparisons to keys while
 * doing any operation. While performing a lookup, each comparison (at most
 * K of them, described above) will perform a single bit comparison against
 * the given key, instead of comparing the entire key to another key.
 * <p>
 * The {@link org.apache.commons.collections4.Trie} can return operations in
 * lexicographical order using the 'prefixMap', 'submap', or 'iterator' methods.
 * The {@link org.apache.commons.collections4.Trie} can also
 * scan for items that are 'bitwise' (using an XOR metric) by the 'select' method.
 * Bitwise closeness is determined by the {@link KeyAnalyzer} returning true or
 * false for a bit being set or not in a given key.
 * <p>
 * This PATRICIA {@link org.apache.commons.collections4.Trie} supports both variable
 * length &amp; fixed length keys. Some methods, such as {@link #prefixMap(Object)}
 * are suited only to variable length keys.
 *
 * @param <E> the type of the values in this map
 *
 * @see <a href="http://en.wikipedia.org/wiki/Radix_tree">Radix Tree</a>
 * @see <a href="http://www.csse.monash.edu.au/~lloyd/tildeAlgDS/Tree/PATRICIA">PATRICIA</a>
 * @see <a href="http://www.imperialviolet.org/binary/critbit.pdf">Crit-Bit Tree</a>
 * @since 4.0
 */
public class PatriciaTrie<E> extends AbstractPatriciaTrie<String, E> {

    private static final long serialVersionUID = 4446367780901817838L;

    public PatriciaTrie() {
        super(new StringKeyAnalyzer());
    }

    public PatriciaTrie(final Map<? extends String, ? extends E> m) {
        super(new StringKeyAnalyzer(), m);
    }

}
