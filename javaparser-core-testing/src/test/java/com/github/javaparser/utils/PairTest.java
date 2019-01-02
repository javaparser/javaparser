package com.github.javaparser.utils;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

class PairTest {
    @Test
    void testToString() {
        Pair<String, String> pair = new Pair<>("abc", "def");

        assertEquals("<abc, def>", pair.toString());
    }

    @Test
    void testToStringNulls() {
        Pair<String, String> pair = new Pair<>(null, null);

        assertEquals("<null, null>", pair.toString());
    }
}
