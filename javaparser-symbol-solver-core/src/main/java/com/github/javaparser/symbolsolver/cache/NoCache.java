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

import java.util.Optional;

/**
 * A cache implementation that does not store any information.
 *
 * @param <K> The key type.
 * @param <V> The value type.
 */
public class NoCache<K, V> implements Cache<K, V> {

    /**
     * Create a new instance.
     *
     * @param <expectedK> The expected type for the key.
     * @param <expectedV> The expected type for the value.
     *
     * @return A newly created instance of {@link NoCache}.
     */
    public static <expectedK, expectedV> NoCache<expectedK, expectedV> create() {
        return new NoCache<>();
    }

    @Override
    public void put(K key, V value) {
        // Nothing to do here.
    }

    @Override
    public Optional<V> get(K key) {
        return Optional.empty();
    }

    @Override
    public void remove(K key) {
        // Nothing to do here.
    }

    @Override
    public void removeAll() {
        // Nothing to do here.
    }

    @Override
    public boolean contains(K key) {
        return false;
    }

    @Override
    public long size() {
        return 0;
    }

    @Override
    public boolean isEmpty() {
        return true;
    }

}
