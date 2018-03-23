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

import org.junit.Test;

import java.io.IOException;

import static org.junit.Assert.assertEquals;

public class RangeTest {

    @Test
    public void aRangeContainsItself() throws IOException {
        Range r = Range.range(1, 1, 3, 10);
        assertEquals(true, r.contains(r));
    }

    @Test
    public void aRangeDoesNotStrictlyContainsItself() throws IOException {
        Range r = Range.range(1, 1, 3, 10);
        assertEquals(false, r.strictlyContains(r));
    }

    @Test
    public void overlappingButNotContainedRangesAreNotOnContains() throws IOException {
        Range r1 = Range.range(1, 1, 3, 10);
        Range r2 = Range.range(2, 1, 7, 10);
        assertEquals(false, r1.contains(r2));
        assertEquals(false, r2.contains(r1));
    }

    @Test
    public void overlappingButNotContainedRangesAreNotOnStrictlyContains() throws IOException {
        Range r1 = Range.range(1, 1, 3, 10);
        Range r2 = Range.range(2, 1, 7, 10);
        assertEquals(false, r1.strictlyContains(r2));
        assertEquals(false, r2.strictlyContains(r1));
    }

    @Test
    public void unrelatedRangesAreNotOnContains() throws IOException {
        Range r1 = Range.range(1, 1, 3, 10);
        Range r2 = Range.range(5, 1, 7, 10);
        assertEquals(false, r1.contains(r2));
        assertEquals(false, r2.contains(r1));
    }

    @Test
    public void unrelatedRangesAreNotOnStrictlyContains() throws IOException {
        Range r1 = Range.range(1, 1, 3, 10);
        Range r2 = Range.range(5, 1, 7, 10);
        assertEquals(false, r1.strictlyContains(r2));
        assertEquals(false, r2.strictlyContains(r1));
    }

    @Test
    public void strictlyContainedRangesOnContains() throws IOException {
        Range r1 = Range.range(1, 1, 3, 10);
        Range r2 = Range.range(2, 1, 3, 4);
        assertEquals(true, r1.contains(r2));
        assertEquals(false, r2.contains(r1));
    }

    @Test
    public void strictlyContainedRangesOnStrictlyContains() throws IOException {
        Range r1 = Range.range(1, 1, 3, 10);
        Range r2 = Range.range(2, 1, 3, 4);
        assertEquals(true, r1.strictlyContains(r2));
        assertEquals(false, r2.strictlyContains(r1));
    }

    @Test
    public void containsConsiderLines() {
        Range r1 = Range.range(22, 9, 22, 29);
        Range r2 = Range.range(26, 19, 26, 28);
        assertEquals(false, r1.contains(r2));
        assertEquals(false, r2.contains(r1));
    }

}
