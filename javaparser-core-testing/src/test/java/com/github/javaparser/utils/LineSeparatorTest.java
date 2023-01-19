/*
 * Copyright (C) 2013-2023 The JavaParser Team.
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

package com.github.javaparser.utils;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * @author Roger Howell
 */
class LineSeparatorTest {

    @Test
    void escaped() {
        assertEquals("\\r", LineSeparator.CR.asEscapedString());
        assertEquals("\\n", LineSeparator.LF.asEscapedString());
        assertEquals("\\r\\n", LineSeparator.CRLF.asEscapedString());
    }

    @Test
    void lookup() {
        assertEquals(LineSeparator.CR, LineSeparator.lookup("\r").get());
        assertEquals(LineSeparator.LF, LineSeparator.lookup("\n").get());
        assertEquals(LineSeparator.CRLF, LineSeparator.lookup("\r\n").get());

        assertFalse(LineSeparator.lookup("").isPresent());
        assertFalse(LineSeparator.lookup(" ").isPresent());
        assertFalse(LineSeparator.lookup("\\r").isPresent());
        assertFalse(LineSeparator.lookup("\\n").isPresent());
        assertFalse(LineSeparator.lookup(" \\r").isPresent());
        assertFalse(LineSeparator.lookup(" \\n").isPresent());
        assertFalse(LineSeparator.lookup("\\r ").isPresent());
        assertFalse(LineSeparator.lookup("\\n ").isPresent());
        assertFalse(LineSeparator.lookup("test 123 123").isPresent());
        assertFalse(LineSeparator.lookup("\r \n").isPresent());
        assertFalse(LineSeparator.lookup("\\r \\n").isPresent());
    }
    
    @Test
    void lookupEscaped() {
        assertEquals(LineSeparator.CR, LineSeparator.lookupEscaped("\\r").get());
        assertEquals(LineSeparator.LF, LineSeparator.lookupEscaped("\\n").get());
        assertEquals(LineSeparator.CRLF, LineSeparator.lookupEscaped("\\r\\n").get());

        assertFalse(LineSeparator.lookupEscaped("").isPresent());
        assertFalse(LineSeparator.lookupEscaped(" ").isPresent());
        assertFalse(LineSeparator.lookupEscaped("\r").isPresent());
        assertFalse(LineSeparator.lookupEscaped("\n").isPresent());
        assertFalse(LineSeparator.lookupEscaped(" \r").isPresent());
        assertFalse(LineSeparator.lookupEscaped(" \n").isPresent());
        assertFalse(LineSeparator.lookupEscaped("\r ").isPresent());
        assertFalse(LineSeparator.lookupEscaped("\n ").isPresent());
        assertFalse(LineSeparator.lookupEscaped("test 123 123").isPresent());
        assertFalse(LineSeparator.lookupEscaped("\r \n").isPresent());
        assertFalse(LineSeparator.lookupEscaped("\\r \\n").isPresent());
    }

    @Test
    void detect() {
        assertEquals(LineSeparator.CR, LineSeparator.detect("\r"));
        assertEquals(LineSeparator.LF, LineSeparator.detect("\n"));
        assertEquals(LineSeparator.CRLF, LineSeparator.detect("\r\n"));

        assertEquals(LineSeparator.NONE, LineSeparator.detect(""));
        assertEquals(LineSeparator.NONE, LineSeparator.detect("test 123 123"));

        assertEquals(LineSeparator.MIXED, LineSeparator.detect("\r \n"));
    }

    @Test
    void testToString() {
        assertEquals("\r", LineSeparator.CR.asRawString());
        assertEquals("\n", LineSeparator.LF.asRawString());
        assertEquals("\r\n", LineSeparator.CRLF.asRawString());

        // Note that this represents an "arbitrary" line ending -- this test is to highlight any time that it changes.
        assertEquals("\n", LineSeparator.ARBITRARY.asRawString());
    }

    @Test
    void values() {
        assertEquals(8, LineSeparator.values().length);
    }

    @Test
    void valueOf() {
        assertEquals(LineSeparator.CR, LineSeparator.valueOf("CR"));
        assertEquals(LineSeparator.LF, LineSeparator.valueOf("LF"));
        assertEquals(LineSeparator.CRLF, LineSeparator.valueOf("CRLF"));
        assertEquals(LineSeparator.NONE, LineSeparator.valueOf("NONE"));
        assertEquals(LineSeparator.MIXED, LineSeparator.valueOf("MIXED"));
        assertEquals(LineSeparator.SYSTEM, LineSeparator.valueOf("SYSTEM"));
        assertEquals(LineSeparator.UNKNOWN, LineSeparator.valueOf("UNKNOWN"));
        assertEquals(LineSeparator.ARBITRARY, LineSeparator.valueOf("ARBITRARY"));
    }

}
