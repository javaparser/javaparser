/*
 * Copyright (C) 2013-2024 The JavaParser Team.
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

package com.github.javaparser.printer.lexicalpreservation;

import static org.junit.jupiter.api.Assertions.*;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.NoSuchElementException;
import org.junit.jupiter.api.*;

class PeekingIteratorTest {

    private static final List<String> EMPTY_LIST = new ArrayList();

    private static List<String> NON_EMPTY_LIST;

    private PeekingIterator<String> peekingIterator;

    @BeforeAll
    static void setUpBeforeClass() throws Exception {}

    @AfterAll
    static void tearDownAfterClass() throws Exception {}

    @BeforeEach
    void setUp() throws Exception {
        NON_EMPTY_LIST = Arrays.asList("A", "B", "C");
    }

    @AfterEach
    void tearDown() throws Exception {}

    @Test
    void testHasNext() {
        peekingIterator = new PeekingIterator(EMPTY_LIST.listIterator());
        assertFalse(peekingIterator.hasNext());
        peekingIterator = new PeekingIterator(NON_EMPTY_LIST.listIterator());
        assertTrue(peekingIterator.hasNext());
    }

    @Test
    void testPeek() {
        peekingIterator = new PeekingIterator(EMPTY_LIST.listIterator());
        assertEquals(null, peekingIterator.peek());
        peekingIterator = new PeekingIterator(NON_EMPTY_LIST.listIterator());
        assertEquals("A", peekingIterator.peek());
        assertEquals("A", peekingIterator.next());
    }

    @Test
    void testElement() {
        peekingIterator = new PeekingIterator(EMPTY_LIST.listIterator());
        assertEquals(null, peekingIterator.peek());
        peekingIterator = new PeekingIterator(NON_EMPTY_LIST.listIterator());
        assertEquals("A", peekingIterator.peek());
        assertEquals(1, peekingIterator.nextIndex());
    }

    @Test
    void testNext() {
        peekingIterator = new PeekingIterator(EMPTY_LIST.listIterator());
        assertThrows(NoSuchElementException.class, () -> peekingIterator.next());
        peekingIterator = new PeekingIterator(NON_EMPTY_LIST.listIterator());
        assertEquals("A", peekingIterator.next());
    }

    @Test
    void testRemove() {
        peekingIterator = new PeekingIterator(EMPTY_LIST.listIterator());
        assertThrows(IllegalStateException.class, () -> peekingIterator.remove());
        peekingIterator = new PeekingIterator(NON_EMPTY_LIST.listIterator());
        assertThrows(IllegalStateException.class, () -> peekingIterator.remove());
        String result = peekingIterator.next();
        assertThrows(UnsupportedOperationException.class, () -> peekingIterator.remove());
    }

    @Test
    void testHasPrevious() {
        peekingIterator = new PeekingIterator(EMPTY_LIST.listIterator());
        assertFalse(peekingIterator.hasPrevious());
        peekingIterator = new PeekingIterator(NON_EMPTY_LIST.listIterator());
        assertFalse(peekingIterator.hasPrevious());
        String result = peekingIterator.next();
        assertTrue(peekingIterator.hasPrevious());
    }

    @Test
    void testPrevious() {
        peekingIterator = new PeekingIterator(EMPTY_LIST.listIterator());
        assertThrows(NoSuchElementException.class, () -> peekingIterator.previous());
        peekingIterator = new PeekingIterator(NON_EMPTY_LIST.listIterator());
        assertThrows(NoSuchElementException.class, () -> peekingIterator.previous());
    }

    @Test
    void testNextIndex() {
        peekingIterator = new PeekingIterator(EMPTY_LIST.listIterator());
        assertEquals(0, peekingIterator.nextIndex());
        peekingIterator = new PeekingIterator(NON_EMPTY_LIST.listIterator());
        assertEquals(0, peekingIterator.nextIndex());
    }

    @Test
    void testPreviousIndex() {
        peekingIterator = new PeekingIterator(EMPTY_LIST.listIterator());
        assertEquals(-1, peekingIterator.previousIndex());
        peekingIterator = new PeekingIterator(NON_EMPTY_LIST.listIterator());
        assertEquals(-1, peekingIterator.previousIndex());
    }

    @Test
    void testSet() {
        peekingIterator = new PeekingIterator(EMPTY_LIST.listIterator());
        assertThrows(IllegalStateException.class, () -> peekingIterator.set("D"));
        peekingIterator = new PeekingIterator(NON_EMPTY_LIST.listIterator());
        assertThrows(IllegalStateException.class, () -> peekingIterator.set("D"));
        peekingIterator.next();
        peekingIterator.set("D");
        assertEquals(3, NON_EMPTY_LIST.size());
    }
}
