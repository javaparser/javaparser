/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2026 The JavaParser Team.
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

import static com.github.javaparser.utils.TestUtils.assertEqualsStringIgnoringEol;
import static org.junit.jupiter.api.Assertions.assertEquals;

import org.junit.jupiter.api.Test;

/**
 * Verifies that a trailing line comment (the one whose attribution is fixed for
 * issue #4960) survives a {@link LexicalPreservingPrinter} round-trip unchanged
 * in the positions the issue cares about: after the last parameter, after the
 * closing parenthesis, after a statement and after an enum constant. These are
 * explicit assertions rather than coverage left to chance.
 */
public class Issue4960Test extends AbstractLexicalPreservingTest {

    private String roundTrip(String code) {
        considerCode(code);
        return LexicalPreservingPrinter.print(cu);
    }

    @Test
    void lppPreservesTrailingCommentAfterLastParameter() {
        String code = "class C {\n" + "    void a(int a //something\n" + "        ) {}\n" + "}\n";
        assertEquals(code, roundTrip(code));
    }

    @Test
    void lppPreservesTrailingCommentAfterClosingParen() {
        String code = "class C {\n" + "    void a(int a) //something\n" + "    {}\n" + "}\n";
        assertEquals(code, roundTrip(code));
    }

    @Test
    void lppPreservesTrailingCommentAfterStatement() {
        String code = "class C {\n" + "    void a() {\n" + "        int x = 1; //something\n" + "    }\n" + "}\n";
        assertEquals(code, roundTrip(code));
    }

    @Test
    void lppPreservesTrailingCommentAfterEnumConstant() {
        String code = "enum E {\n" + "    A, //something\n" + "    B;\n" + "}\n";
        assertEquals(code, roundTrip(code));
    }

    @Test
    void lppPreservesCommentAfterLastParameterWithTwoParameters() {
        // A line comment after the last of several parameters: it must not be
        // duplicated onto the earlier parameter during the round-trip.
        String code = "class C {\n" + "    void a(int a, int b //something\n" + "        ) {}\n" + "}\n";
        String printed = roundTrip(code);
        assertEqualsStringIgnoringEol(code, printed);
        assertEquals(1, countOccurrences(printed, "//something"));
    }

    private static int countOccurrences(String haystack, String needle) {
        int count = 0;
        int from = 0;
        while (true) {
            int idx = haystack.indexOf(needle, from);
            if (idx < 0) {
                break;
            }
            count++;
            from = idx + needle.length();
        }
        return count;
    }
}
