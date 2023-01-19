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

import java.util.Objects;
import java.util.Optional;

/**
 * This class is used to wrap a Guava {@link com.google.common.cache.Cache}.
 *
 * @param <K> The type of the key.
 * @param <V> The type of the value.
 */
public class GuavaCache<K, V> implements Cache<K, V>  {

    /**
     * Wrap a Guava cache with a custom cache.
     *
     * @param guavaCache The guava cache to be wrapped-
     *
     * @param <expectedK> The expected type for the key.
     * @param <expectedV> The expected type for the value.
     *
     * @return A newly created instance of {@link NoCache}.
     */
    public static <expectedK, expectedV> GuavaCache<expectedK, expectedV> create(com.google.common.cache.Cache<expectedK, expectedV> guavaCache) {
        return new GuavaCache<>(guavaCache);
    }

    private final com.google.common.cache.Cache<K, V> guavaCache;

    public GuavaCache(com.google.common.cache.Cache<K, V> guavaCache) {
        this.guavaCache = Objects.requireNonNull(guavaCache, "The argument GuavaCache can't be null.");
    }

    @Override
    public void put(K key, V value) {
        guavaCache.put(key, value);
    }

    @Override
    public Optional<V> get(K key) {
        return Optional.ofNullable(
                guavaCache.getIfPresent(key)
        );
    }

    @Override
    public void remove(K key) {
        guavaCache.invalidate(key);
    }

    @Override
    public void removeAll() {
        guavaCache.invalidateAll();
    }

    @Override
    public boolean contains(K key) {
        return get(key).isPresent();
    }

    @Override
    public long size() {
        return guavaCache.size();
    }

    @Override
    public boolean isEmpty() {
        return size() == 0;
    }

}
