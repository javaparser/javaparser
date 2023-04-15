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

package com.github.javaparser;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class RangeTest {

    private final Position pos1 = new Position(10, 11);
    private final Position pos2 = new Position(20, 21);
    private final Range range_orderedPositions = Range.range(pos1, pos2);
    private final Range range_reversedPositions = Range.range(pos2, pos1);

    private final Position posA1 = new Position(1, 1);
    private final Position posB1 = new Position(2, 1);
    private final Position posC1 = new Position(3, 1);
    private final Position posD1 = new Position(4, 1);
    private final Position posE1 = new Position(5, 1);

    private final Position posA5 = new Position(1, 5);
    private final Position posB5 = new Position(2, 5);
    private final Position posC5 = new Position(3, 5);
    private final Position posD5 = new Position(4, 5);
    private final Position posE5 = new Position(5, 5);

    private final Range arbitraryRange = Range.range(1, 1, 3, 10);

    // Potential expansion option for a larger variety of these categories of values to be provided to parameterised tests.
    //@formatter:off
    private Range[] rangePair_overlappingButNotContained = new Range[]{Range.range(posA1, posC1), Range.range(posB1, posE1)};
    private Range[] rangePair_unrelated                  = new Range[]{Range.range(posA1, posB1), Range.range(posD1, posE1)};
    private Range[] rangePair_equalBeginEnd              = new Range[]{Range.range(posA1, posB1), Range.range(posA1, posB1)};
    private Range[] rangePair_strictlyContained          = new Range[]{Range.range(posA1, posE1), Range.range(posB1, posD1)};
    private Range[] rangePair_touchingLineAndColumn      = new Range[]{Range.range(posA1, posC1), Range.range(posC1, posE1)};
    private Range[] rangePair_touchingLineNotColumn      = new Range[]{Range.range(posA1, posC1), Range.range(posC5, posD1)};
    //@formatter:on

    @Test
    void constructorWithOrderedPositions() {
        assertEquals(10, range_orderedPositions.begin.line);
        assertEquals(11, range_orderedPositions.begin.column);
        assertEquals(20, range_orderedPositions.end.line);
        assertEquals(21, range_orderedPositions.end.column);
    }

    @Test
    void constructorWithReversedPositions() {
        assertEquals(10, range_reversedPositions.begin.line);
        assertEquals(11, range_reversedPositions.begin.column);
        assertEquals(20, range_reversedPositions.end.line);
        assertEquals(21, range_reversedPositions.end.column);
    }

    @Test
    void rangePair_equalBeginEnd_contains_true() {
        assertTrue(rangePair_equalBeginEnd[0].contains(rangePair_equalBeginEnd[1]));
    }

    @Test
    void rangePair_equalBeginEnd_strictlyContains_false() {
        assertFalse(rangePair_equalBeginEnd[0].strictlyContains(rangePair_equalBeginEnd[1]));
    }

    @Test
    void rangePair_overlappingButNotContained_contains_false() {
        Range r1 = rangePair_overlappingButNotContained[0];
        Range r2 = rangePair_overlappingButNotContained[1];
        assertFalse(r1.contains(r2));
        assertFalse(r2.contains(r1));
    }

    @Test
    void rangePair_overlappingButNotContained_strictlyContains_false() {
        Range r1 = rangePair_overlappingButNotContained[0];
        Range r2 = rangePair_overlappingButNotContained[1];
        assertFalse(r1.strictlyContains(r2));
        assertFalse(r2.strictlyContains(r1));
    }

    @Test
    void rangePair_unrelated_contains_false() {
        Range r1 = rangePair_unrelated[0];
        Range r2 = rangePair_unrelated[1];
        assertFalse(r1.contains(r2));
        assertFalse(r2.contains(r1));
    }

    @Test
    void rangePair_unrelated_strictlyContains_false() {
        Range r1 = rangePair_unrelated[0];
        Range r2 = rangePair_unrelated[1];
        assertFalse(r1.strictlyContains(r2));
        assertFalse(r2.strictlyContains(r1));
    }

    @Test
    void rangePair_strictlyContained_contains() {
        Range r1 = rangePair_strictlyContained[0];
        Range r2 = rangePair_strictlyContained[1];
        assertTrue(r1.contains(r2));
        assertFalse(r2.contains(r1));
    }

    @Test
    void rangePair_strictlyContained_strictlyContains() {
        Range r1 = rangePair_strictlyContained[0];
        Range r2 = rangePair_strictlyContained[1];
        assertTrue(r1.strictlyContains(r2));
        assertFalse(r2.strictlyContains(r1));
    }

    @Test
    void rangePair_touchingLineAndColumn_contains() {
        Range r1 = rangePair_touchingLineAndColumn[0];
        Range r2 = rangePair_touchingLineAndColumn[1];
        assertFalse(r1.contains(r2));
        assertFalse(r2.contains(r1));
    }

    @Test
    void rangePair_touchingLineAndColumn_strictlyContains() {
        Range r1 = rangePair_touchingLineAndColumn[0];
        Range r2 = rangePair_touchingLineAndColumn[1];
        assertFalse(r1.strictlyContains(r2));
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
    void rangePair_touchingLineAndColumn_overlapsAccountsForColumn_true() {
        Range r1 = rangePair_touchingLineAndColumn[0];
        Range r2 = rangePair_touchingLineAndColumn[1];
        assertTrue(r1.overlapsWith(r2));
        assertTrue(r2.overlapsWith(r1));
    }

    @Test
    void rangePair_touchingLineNotColumn_overlapsAccountsForColumn_false() {
        Range r1 = rangePair_touchingLineNotColumn[0];
        Range r2 = rangePair_touchingLineNotColumn[1];
        assertFalse(r1.overlapsWith(r2));
        assertFalse(r2.overlapsWith(r1));
    }


    @Test
    void lineCountIsReturned() {
        Range r1 = Range.range(1, 1, 5, 2);
        assertEquals(5, r1.getLineCount());

        Range r2 = Range.range(26, 5, 57, 6);
        assertEquals(32, r2.getLineCount());
    }

    @Test
    void arbitraryRange_containsItsBegin_true() {
        Range r = arbitraryRange;
        assertTrue(r.contains(r.begin));
    }

    @Test
    void arbitraryRange_containsItsEnd_true() {
        Range r = arbitraryRange;
        assertTrue(r.contains(r.end));
    }

    @Test
    void arbitraryRange_strictlyContainItsBegin_false() {
        Range r = arbitraryRange;
        assertFalse(r.strictlyContains(r.begin));
    }

    @Test
    void arbitraryRange_strictlyContainItsEnd_false() {
        Range r = arbitraryRange;
        assertFalse(r.strictlyContains(r.end));
    }
@Test
    void touchingLineColumnRangesOverlap() {
        Range r1 = Range.range(1, 1, 3, 10);
        Range r2 = Range.range(3, 10, 5, 10);
        assertTrue(r1.overlapsWith(r2));
        assertTrue(r2.overlapsWith(r1));
    }

    @Test
    void touchingLineNotColumnRangesDoNotOverlap() {
        Range r1 = Range.range(1, 1, 3, 5);
        Range r2 = Range.range(3, 10, 5, 10);
        assertFalse(r1.overlapsWith(r2));
        assertFalse(r2.overlapsWith(r1));
    }
    @Test
    void rangePair_equalBeginEnd_overlap_true() {
        Range r1 = rangePair_equalBeginEnd[0];
        Range r2 = rangePair_equalBeginEnd[1];
        assertTrue(r1.overlapsWith(r2));
        assertTrue(r2.overlapsWith(r1));
    }

    @Test
    void rangePair_unrelated_overlap_false() {
        Range r1 = rangePair_unrelated[0];
        Range r2 = rangePair_unrelated[1];
        assertFalse(r1.overlapsWith(r2));
        assertFalse(r2.overlapsWith(r1));
    }

    @Test
    void rangePair_touchingLineAndColumn_overlap_false() {
        Range r1 = rangePair_touchingLineAndColumn[0];
        Range r2 = rangePair_touchingLineAndColumn[1];
        assertTrue(r1.overlapsWith(r2));
        assertTrue(r2.overlapsWith(r1));
    }

    @Test
    void rangePair_overlappingButNotContained_overlap_true() {
        Range r1 = rangePair_overlappingButNotContained[0];
        Range r2 = rangePair_overlappingButNotContained[1];
        assertTrue(r1.overlapsWith(r2));
        assertTrue(r2.overlapsWith(r1));
    }

    @Test
    void rangePair_strictlyContained_overlap_true() {
        Range r1 = rangePair_strictlyContained[0];
        Range r2 = rangePair_strictlyContained[1];
        assertTrue(r1.overlapsWith(r2));
        assertTrue(r2.overlapsWith(r1));
    }
    
    @Test
    void rangePair_is_before() {
        Range r1 = Range.range(new Position(1,1), new Position(1,2));
        Range r2 = Range.range(new Position(1,3), new Position(1,4));
        assertTrue(r1.isBefore(r2));
    }
    
    @Test
    void rangePair_is_not_before() {
        Range r1 = Range.range(new Position(1,1), new Position(1,2));
        Range r2 = Range.range(new Position(1,3), new Position(1,4));
        Range r3 = Range.range(new Position(1,1), new Position(1,4));
        assertFalse(r2.isBefore(r1));
        assertFalse(r3.isBefore(r1));
    }
    
    @Test
    void rangePair_is_after() {
        Range r1 = Range.range(new Position(1,1), new Position(1,2));
        Range r2 = Range.range(new Position(1,3), new Position(1,4));
        assertTrue(r2.isAfter(r1));
    }
    
    @Test
    void rangePair_is_not_after() {
        Range r1 = Range.range(new Position(1,1), new Position(1,2));
        Range r2 = Range.range(new Position(1,3), new Position(1,4));
        Range r3 = Range.range(new Position(1,1), new Position(1,4));
        assertFalse(r1.isAfter(r2));
        assertFalse(r1.isAfter(r3));
    }

}
