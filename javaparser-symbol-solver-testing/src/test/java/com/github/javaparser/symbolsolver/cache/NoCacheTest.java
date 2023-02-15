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

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class NoCacheTest {

    private final NoCache<Object, Object> cache = new NoCache<>();

    @Test
    void create_ShouldCreateDifferentCache() {
        NoCache<Object, Object> firstCache = NoCache.create();
        assertNotNull(firstCache);

        NoCache<Object, Object> secondCache = NoCache.create();
        assertNotNull(secondCache);
        assertNotEquals(firstCache, secondCache);
    }

    @Test
    void put_shouldNotRegisterTheKey() {
        assertEquals(0, cache.size());
        cache.put("key", "value");
        assertEquals(0, cache.size());
    }

    @Test
    void get_ShouldNotBePresent() {
        assertFalse(cache.get("key").isPresent());
    }

    @Test
    void remove_ShouldDoNothing() {
        assertEquals(0, cache.size());
        cache.remove("key");
        assertEquals(0, cache.size());
    }

    @Test
    void removeAll_ShouldDoNothing() {
        assertEquals(0, cache.size());
        cache.removeAll();
        assertEquals(0, cache.size());
    }

    @Test
    void contains_ShouldNotContainsKey() {
        assertFalse(cache.contains("key"));
    }

    @Test
    void size_ShouldHaveSizeOfZero() {
        assertEquals(0, cache.size());
    }

    @Test
    void isEmpty_ShouldAlwaysBeTrue() {
        assertTrue(cache.isEmpty());
    }

}