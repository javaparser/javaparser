package com.github.javaparser.utils;

import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class PairTest {
    @Test
    public void testToString() {
        Pair<String, String> pair = new Pair<>("abc", "def");

        assertEquals("<abc, def>", pair.toString());
    }

    @Test
    public void testToStringNulls() {
        Pair<String, String> pair = new Pair<>(null, null);

        assertEquals("<null, null>", pair.toString());
    }
}
