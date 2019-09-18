/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2016 The JavaParser Team.
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

package com.github.javaparser;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class RangeTest {

    @Test
    void aRangeContainsItself() {
        Range r = Range.range(1, 1, 3, 10);
        assertTrue(r.contains(r));
    }

    @Test
    void aRangeDoesNotStrictlyContainsItself() {
        Range r = Range.range(1, 1, 3, 10);
        assertFalse(r.strictlyContains(r));
    }

    @Test
    void overlappingButNotContainedRangesAreNotOnContains() {
        Range r1 = Range.range(1, 1, 3, 10);
        Range r2 = Range.range(2, 1, 7, 10);
        assertFalse(r1.contains(r2));
        assertFalse(r2.contains(r1));
    }

    @Test
    void overlappingButNotContainedRangesAreNotOnStrictlyContains() {
        Range r1 = Range.range(1, 1, 3, 10);
        Range r2 = Range.range(2, 1, 7, 10);
        assertFalse(r1.strictlyContains(r2));
        assertFalse(r2.strictlyContains(r1));
    }

    @Test
    void unrelatedRangesAreNotOnContains() {
        Range r1 = Range.range(1, 1, 3, 10);
        Range r2 = Range.range(5, 1, 7, 10);
        assertFalse(r1.contains(r2));
        assertFalse(r2.contains(r1));
    }

    @Test
    void unrelatedRangesAreNotOnStrictlyContains() {
        Range r1 = Range.range(1, 1, 3, 10);
        Range r2 = Range.range(5, 1, 7, 10);
        assertFalse(r1.strictlyContains(r2));
        assertFalse(r2.strictlyContains(r1));
    }

    @Test
    void strictlyContainedRangesOnContains() {
        Range r1 = Range.range(1, 1, 3, 10);
        Range r2 = Range.range(2, 1, 3, 4);
        assertTrue(r1.contains(r2));
        assertFalse(r2.contains(r1));
    }

    @Test
    void strictlyContainedRangesOnStrictlyContains() {
        Range r1 = Range.range(1, 1, 3, 10);
        Range r2 = Range.range(2, 1, 3, 4);
        assertTrue(r1.strictlyContains(r2));
        assertFalse(r2.strictlyContains(r1));
    }

    @Test
    void containsConsiderLines() {
        Range r1 = Range.range(22, 9, 22, 29);
        Range r2 = Range.range(26, 19, 26, 28);
        assertFalse(r1.contains(r2));
        assertFalse(r2.contains(r1));
    }

    @Test
    void lineCountIsReturned() {
        Range r1 = Range.range(1, 1, 5, 2);
        Range r2 = Range.range(26, 5, 57, 6);
        assertEquals(5, r1.getLineCount());
        assertEquals(32, r2.getLineCount());
    }
    
    @Test
    void aRangeContainsItsBegin() {
        Range r = Range.range(1, 1, 3, 10);
        assertTrue(r.contains(r.begin));
    }

    @Test
    void aRangeContainsItsEnd() {
        Range r = Range.range(1, 1, 3, 10);
        assertTrue(r.contains(r.end));
    }
    
    @Test
    void aRangeDoesntStrictlyContainItsBegin() {
        Range r = Range.range(1, 1, 3, 10);
        assertFalse(r.strictlyContains(r.begin));
    }

    @Test
    void aRangeDoesntStrictlyContainItsEnd() {
        Range r = Range.range(1, 1, 3, 10);
        assertFalse(r.strictlyContains(r.end));
    }
    
    @Test
    void rangesOverlap() {
        Range r1 = Range.range(1, 1, 3, 10);
        Range r2 = Range.range(3, 5, 5, 10);
        assertTrue(r1.overlapsWith(r2));
        assertTrue(r2.overlapsWith(r1));
    }
    
    @Test
    void rangesDoNotOverlap() {
        Range r1 = Range.range(1, 1, 3, 10);
        Range r2 = Range.range(4, 11, 5, 10);
        assertFalse(r1.overlapsWith(r2));
        assertFalse(r2.overlapsWith(r1));
    }
    
    @Test
    void strictlyContainedRangesOverlap() {
        Range r1 = Range.range(1, 1, 3, 10);
        Range r2 = Range.range(2, 1, 3, 4);
        assertTrue(r1.overlapsWith(r2));
        assertTrue(r2.overlapsWith(r1));
    }

}
