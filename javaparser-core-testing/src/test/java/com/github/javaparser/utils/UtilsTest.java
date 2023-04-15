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

package com.github.javaparser.utils;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.io.Reader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Optional;

import static com.github.javaparser.utils.Utils.assertNotNull;
import static com.github.javaparser.utils.Utils.*;
import static org.junit.jupiter.api.Assertions.*;

class UtilsTest {

    @Test
    void testIsNullOrEmpty() {
        assertTrue(isNullOrEmpty(null));
        assertTrue(isNullOrEmpty(new ArrayList<>()));

        assertFalse(isNullOrEmpty(
                new ArrayList<>(Arrays.asList("foo", "bar"))));
    }

    @Test
    void testAssertNotNull() {
        assertEquals("foo", assertNotNull("foo"));
        assertThrows(AssertionError.class, () -> assertNotNull(null));
    }

    @Test
    void testAssertNonEmpty() {
        assertEquals("foo", assertNonEmpty("foo"));
        assertThrows(AssertionError.class, () -> assertNonEmpty(""));
        assertThrows(AssertionError.class, () -> assertNonEmpty(null));

    }

    @Test
    void testAssertNonNegative() {
        assertEquals((Number) 2, assertNonNegative(2));
        assertThrows(AssertionError.class, () -> assertNonNegative(-2));
    }

    @Test
    void testAssertPositive() {
        assertEquals((Number) 2, assertPositive(2));
        assertThrows(AssertionError.class, () -> assertPositive(-2));
    }

    @Test
    void testEscapeEndOfLines() {
        assertEquals("f\\no\\ro", escapeEndOfLines("f\no\ro"));
    }

    @Test
    void testReaderToString() throws IOException {
        Reader reader = new Reader() {
            @Override
            public int read(char[] chars, int i, int i1) throws IOException {
                return 0;
            }

            @Override
            public void close() throws IOException {
            }
        };
        assertEquals("", readerToString(reader));
    }

    @Test
    void testToCamelCase() {
        assertEquals("foo", toCamelCase("foo"));
        assertEquals("foo", toCamelCase("Foo"));
        assertEquals("foo", toCamelCase("FOO"));
        assertEquals("foo", toCamelCase("fOo"));
    }

    @Test
    void testScreamingToCamelCase() {
        assertEquals("abc", screamingToCamelCase("ABC"));
        assertEquals("abcDef", screamingToCamelCase("ABC_DEF"));
        assertEquals("abc", screamingToCamelCase("ABC_"));
    }

    @Test
    void screamingEmptyString() {
        assertEquals("", camelCaseToScreaming(""));
        assertEquals("ABC", camelCaseToScreaming("abc"));
        assertEquals("HELLO_HELLO", camelCaseToScreaming("HelloHello"));
        assertEquals("APE_TAIL", camelCaseToScreaming("apeTail"));
    }

    @Test
    void testNextWord() {
        assertEquals("foo", nextWord("foo"));
        assertEquals("foo", nextWord("foo bar"));
        assertEquals("foo", nextWord("foo bar Baz"));
    }

    @Test
    void testIndent() {
        assertEquals("foo",
                indent(new StringBuilder("foo"), 0).toString());
        assertEquals("foo\t",
                indent(new StringBuilder("foo"), 1).toString());
        assertEquals("foo\t\t",
                indent(new StringBuilder("foo"), 2).toString());
        assertEquals("foo\t\t\t",
                indent(new StringBuilder("foo"), 3).toString());
    }

    @Test
    void capitalizeOnEmptyString() {
        assertThrows(IllegalArgumentException.class, () -> capitalize(""));
    }

    @Test
    void capitalizeOnStringOfOneCharacter() {
        assertEquals("F", capitalize("f"));
    }

    @Test
    void capitalizeOnStringOfTwoCharacters() {
        assertEquals("Fo", capitalize("fo"));
    }

    @Test
    void decapitalizeOnEmptyString() {
        assertThrows(IllegalArgumentException.class, () -> decapitalize(""));
    }

    @Test
    void decapitalizeOnStringOfOneCharacter() {
        assertEquals("f", decapitalize("F"));
    }

    @Test
    void decapitalizeOnStringOfTwoCharacters() {
        assertEquals("fo", decapitalize("Fo"));
    }

    @Test
    void testValueIsNullOrEmpty() {
        assertTrue(valueIsNullOrEmpty(null));
        assertTrue(valueIsNullOrEmpty(Optional.empty()));
        assertTrue(valueIsNullOrEmpty(new ArrayList<>()));

        assertFalse(valueIsNullOrEmpty(
                Optional.ofNullable("foo")));
        assertFalse(valueIsNullOrEmpty(
                new ArrayList<>(Arrays.asList("foo", "bar"))));
    }

    @Test
    void testValueIsNullOrEmptyStringOrOptional() {
        assertTrue(valueIsNullOrEmptyStringOrOptional(null));
        assertTrue(valueIsNullOrEmptyStringOrOptional(
                Optional.empty()));

        assertFalse(valueIsNullOrEmptyStringOrOptional("foo"));
        assertFalse(valueIsNullOrEmptyStringOrOptional(
                Optional.ofNullable("foo")));
    }

    @Test
    void testIndexOfElementByObjectIdentity() {
        assertEquals(-1, indexOfElementByObjectIdentity(
                new ArrayList<>(), "bar"));
        assertEquals(1, indexOfElementByObjectIdentity(
                new ArrayList<>(Arrays.asList("foo", "bar")), "bar"));
    }

    @Test
    void testSet() {
        assertEquals(new HashSet<>(Arrays.asList("bar", "foo", "baz")),
                set("foo", "bar", "baz"));
    }

    @Test
    void normalizeEolInTextBlock() {
        String result = Utils.normalizeEolInTextBlock("\r\n \r \n", "Q");
        assertEquals("Q Q Q", result);
    }

    @Test
    void testRemoveFileExtension() {
        assertEquals("foo", removeFileExtension("foo"));
        assertEquals("foo", removeFileExtension("foo.txt"));
    }

    @Test
    void testTrimTrailingSpaces() {
        assertEquals("abc", trimTrailingSpaces("abc"));
        assertEquals("  abc", trimTrailingSpaces("  abc"));
        assertEquals("abc", trimTrailingSpaces("abc  "));
        assertEquals("  abc", trimTrailingSpaces("  abc  "));
        assertEquals("abc", trimTrailingSpaces("abc\t\0"));
        assertEquals("", trimTrailingSpaces("    "));
        assertEquals("", trimTrailingSpaces(""));
    }
}
