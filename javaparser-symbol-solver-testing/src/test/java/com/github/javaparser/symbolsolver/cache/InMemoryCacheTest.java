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

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.Optional;

import static org.junit.jupiter.api.Assertions.*;

class InMemoryCacheTest {

    private InMemoryCache<Object, Object> memoryCache;

    @BeforeEach
    void beforeEach() {
        memoryCache = InMemoryCache.create();
    }

    @Test
    void put_ShouldStoreTheValue() {
        assertTrue(memoryCache.isEmpty());
        assertFalse(memoryCache.contains("key"));

        memoryCache.put("key", "");
        assertFalse(memoryCache.isEmpty());
        assertTrue(memoryCache.contains("key"));
    }

    @Test
    void get_ShouldReturnTheCachedValue() {
        memoryCache.put("foo", "bar");
        memoryCache.put("rab", "oof");

        String key = "key";
        String value = "value";

        assertFalse(memoryCache.get(key).isPresent(), "No value expected at the moment");

        memoryCache.put(key, value);
        Optional<Object> cachedValue = memoryCache.get(key);
        assertTrue(cachedValue.isPresent(), "No value expected at the moment");
        assertEquals(value, cachedValue.get(), "The values seem to be different");

        memoryCache.remove(key);
        assertFalse(memoryCache.get(key).isPresent(), "No value expected at the moment");
    }

    @Test
    void remove_ShouldOnlyRemoveTheKey() {

        // Prepare the values
        String key1 = "key1";
        String key2 = "key2";
        String key3 = "key3";

        memoryCache.put(key1, "");
        memoryCache.put(key2, "");
        memoryCache.put(key3, "");

        assertEquals(3, memoryCache.size());
        assertTrue(memoryCache.contains(key1));
        assertTrue(memoryCache.contains(key2));
        assertTrue(memoryCache.contains(key3));

        // Remove second element
        memoryCache.remove(key2);
        assertEquals(2, memoryCache.size());
        assertTrue(memoryCache.contains(key1));
        assertFalse(memoryCache.contains(key2));
        assertTrue(memoryCache.contains(key3));

        // Remove the third element
        memoryCache.remove(key3);
        assertEquals(1, memoryCache.size());
        assertTrue(memoryCache.contains(key1));
        assertFalse(memoryCache.contains(key3));

        // Remove first element
        memoryCache.remove(key1);
        assertEquals(0, memoryCache.size());
        assertFalse(memoryCache.contains(key2));
    }

    @Test
    void removeAll_ShouldRemoveAllTheKeys() {
        memoryCache.put("key1", "");
        memoryCache.put("key2", "");
        memoryCache.put("key3", "");

        assertFalse(memoryCache.isEmpty());
        memoryCache.removeAll();
        assertTrue(memoryCache.isEmpty());
    }

    @Test
    void contains_ShouldOnlyReturnTrue_WhenTheKeyExists() {
        String key = "key";

        assertFalse(memoryCache.contains(key), "At this moment, the key should not exists.");
        memoryCache.put(key, "value");
        assertTrue(memoryCache.contains(key), "At this moment, the key should be registered.");
        memoryCache.remove(key);
        assertFalse(memoryCache.contains(key), "At this moment, the key should not exists.");
    }

    @Test
    void isEmpty_ShouldOnlyReturnTrue_WhenTheSizeIsZero() {
        String key = "key";

        assertTrue(memoryCache.isEmpty());

        memoryCache.put(key, "value");
        assertFalse(memoryCache.isEmpty());

        memoryCache.remove(key);
        assertTrue(memoryCache.isEmpty());
    }

}