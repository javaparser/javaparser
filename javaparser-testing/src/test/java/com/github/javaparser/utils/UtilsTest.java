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

package com.github.javaparser.utils;

import org.junit.Test;

import static com.github.javaparser.utils.Utils.*;
import static org.junit.Assert.assertEquals;

public class UtilsTest {

    @Test
    public void testScreamingToCamelCase() {
        assertEquals("abc", screamingToCamelCase("ABC"));
        assertEquals("abcDef", screamingToCamelCase("ABC_DEF"));
        assertEquals("abc", screamingToCamelCase("ABC_"));
    }

    @Test
    public void screamingEmptyString() {
        assertEquals("", camelCaseToScreaming(""));
        assertEquals("ABC", camelCaseToScreaming("abc"));
        assertEquals("HELLO_HELLO", camelCaseToScreaming("HelloHello"));
        assertEquals("APE_TAIL", camelCaseToScreaming("apeTail"));
    }

    @Test(expected = IllegalArgumentException.class)
    public void capitalizeOnEmptyString() {
        capitalize("");
    }

    @Test
    public void capitalizeOnStringOfOneCharacter() {
        assertEquals("F", capitalize("f"));
    }

    @Test
    public void capitalizeOnStringOfTwoCharacters() {
        assertEquals("Fo", capitalize("fo"));
    }

    @Test(expected = IllegalArgumentException.class)
    public void decapitalizeOnEmptyString() {
        decapitalize("");
    }

    @Test
    public void decapitalizeOnStringOfOneCharacter() {
        assertEquals("f", decapitalize("F"));
    }

    @Test
    public void decapitalizeOnStringOfTwoCharacters() {
        assertEquals("fo", decapitalize("Fo"));
    }
    
    @Test
    public void normalizeEolInTextBlock() {
        String result = Utils.normalizeEolInTextBlock("\r\n \r \n", "Q");
        assertEquals("Q Q Q", result);
    }

    @Test
    public void testTrimTrailingSpaces() {
        assertEquals("abc", trimTrailingSpaces("abc"));
        assertEquals("  abc", trimTrailingSpaces("  abc"));
        assertEquals("abc", trimTrailingSpaces("abc  "));
        assertEquals("  abc", trimTrailingSpaces("  abc  "));
        assertEquals("abc", trimTrailingSpaces("abc\t\0"));
        assertEquals("", trimTrailingSpaces("    "));
        assertEquals("", trimTrailingSpaces(""));
    }
}
