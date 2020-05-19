package com.github.javaparser.utils;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * @author Roger Howell
 */
class LineEndingTest {

    @Test
    void escaped() {
        assertEquals("\\r", LineEnding.CR.escaped());
        assertEquals("\\n", LineEnding.LF.escaped());
        assertEquals("\\r\\n", LineEnding.CRLF.escaped());
    }

    @Test
    void lookup() {
        assertEquals(LineEnding.CR, LineEnding.lookup("\r").get());
        assertEquals(LineEnding.LF, LineEnding.lookup("\n").get());
        assertEquals(LineEnding.CRLF, LineEnding.lookup("\r\n").get());

        assertFalse(LineEnding.lookup("").isPresent());
        assertFalse(LineEnding.lookup(" ").isPresent());
        assertFalse(LineEnding.lookup("\\r").isPresent());
        assertFalse(LineEnding.lookup("\\n").isPresent());
        assertFalse(LineEnding.lookup(" \\r").isPresent());
        assertFalse(LineEnding.lookup(" \\n").isPresent());
        assertFalse(LineEnding.lookup("\\r ").isPresent());
        assertFalse(LineEnding.lookup("\\n ").isPresent());
        assertFalse(LineEnding.lookup("test 123 123").isPresent());
        assertFalse(LineEnding.lookup("\r \n").isPresent());
        assertFalse(LineEnding.lookup("\\r \\n").isPresent());
    }
    
    @Test
    void lookupEscaped() {
        assertEquals(LineEnding.CR, LineEnding.lookupEscaped("\\r").get());
        assertEquals(LineEnding.LF, LineEnding.lookupEscaped("\\n").get());
        assertEquals(LineEnding.CRLF, LineEnding.lookupEscaped("\\r\\n").get());

        assertFalse(LineEnding.lookupEscaped("").isPresent());
        assertFalse(LineEnding.lookupEscaped(" ").isPresent());
        assertFalse(LineEnding.lookupEscaped("\r").isPresent());
        assertFalse(LineEnding.lookupEscaped("\n").isPresent());
        assertFalse(LineEnding.lookupEscaped(" \r").isPresent());
        assertFalse(LineEnding.lookupEscaped(" \n").isPresent());
        assertFalse(LineEnding.lookupEscaped("\r ").isPresent());
        assertFalse(LineEnding.lookupEscaped("\n ").isPresent());
        assertFalse(LineEnding.lookupEscaped("test 123 123").isPresent());
        assertFalse(LineEnding.lookupEscaped("\r \n").isPresent());
        assertFalse(LineEnding.lookupEscaped("\\r \\n").isPresent());
    }

    @Test
    void detect() {
        assertEquals(LineEnding.CR, LineEnding.detect("\r"));
        assertEquals(LineEnding.LF, LineEnding.detect("\n"));
        assertEquals(LineEnding.CRLF, LineEnding.detect("\r\n"));

        assertEquals(LineEnding.NONE, LineEnding.detect(""));
        assertEquals(LineEnding.NONE, LineEnding.detect("test 123 123"));

        assertEquals(LineEnding.MIXED, LineEnding.detect("\r \n"));
    }

    @Test
    void testToString() {
        assertEquals("\r", LineEnding.CR.toString());
        assertEquals("\n", LineEnding.LF.toString());
        assertEquals("\r\n", LineEnding.CRLF.toString());

        // Note that this represents an "arbitrary" line ending -- this test is to highlight any time that it changes.
        assertEquals("\n", LineEnding.ARBITRARY.toString());
    }

    @Test
    void values() {
        assertEquals(8, LineEnding.values().length);
    }

    @Test
    void valueOf() {
        assertEquals(LineEnding.CR, LineEnding.valueOf("CR"));
        assertEquals(LineEnding.LF, LineEnding.valueOf("LF"));
        assertEquals(LineEnding.CRLF, LineEnding.valueOf("CRLF"));
        assertEquals(LineEnding.NONE, LineEnding.valueOf("NONE"));
        assertEquals(LineEnding.MIXED, LineEnding.valueOf("MIXED"));
        assertEquals(LineEnding.SYSTEM, LineEnding.valueOf("SYSTEM"));
        assertEquals(LineEnding.UNKNOWN, LineEnding.valueOf("UNKNOWN"));
        assertEquals(LineEnding.ARBITRARY, LineEnding.valueOf("ARBITRARY"));
    }

}
