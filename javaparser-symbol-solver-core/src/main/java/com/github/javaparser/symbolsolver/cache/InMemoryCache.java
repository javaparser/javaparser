/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */

package com.github.javaparser.symbolsolver.cache;

import java.util.Collections;
import java.util.Map;
import java.util.Optional;
import java.util.WeakHashMap;

/**
 * A cache implementation that stores the information in memory.
 * <br>
 * The current implementation stores the values in memory in a {@link WeakHashMap}.
 *
 * @param <K> The type of the key.
 * @param <V> The type of the value.
 */
public class InMemoryCache<K, V> implements Cache<K, V>  {

    /**
     * Create a new instance for a cache in memory.
     *
     * @param <expectedK> The expected type for the key.
     * @param <expectedV> The expected type for the value.
     *
     * @return A newly created instance of {@link InMemoryCache}.
     */
    public static <expectedK, expectedV> InMemoryCache<expectedK, expectedV> create() {
        return new InMemoryCache<>();
    }

    private final Map<K, V> mappedValues;

    private InMemoryCache() {
    	mappedValues = Collections.synchronizedMap(new WeakHashMap<>());
    }

    @Override
    public void put(K key, V value) {
        mappedValues.put(key, value);
    }

    @Override
    public Optional<V> get(K key) {
        return Optional.ofNullable(
                mappedValues.get(key)
        );
    }

    @Override
    public void remove(K key) {
        mappedValues.remove(key);
    }

    @Override
    public void removeAll() {
        mappedValues.clear();
    }

    @Override
    public boolean contains(K key) {
        return mappedValues.containsKey(key);
    }

    @Override
    public long size() {
        return mappedValues.size();
    }

    @Override
    public boolean isEmpty() {
        return mappedValues.isEmpty();
    }

}
