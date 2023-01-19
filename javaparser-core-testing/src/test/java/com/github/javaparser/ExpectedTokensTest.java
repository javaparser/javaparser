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

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.CharLiteralExpr;
import com.github.javaparser.utils.ExtractingVisitors;
import org.junit.jupiter.api.Test;

import java.util.List;

import static com.github.javaparser.utils.TestUtils.getNodeStartingAtPosition;
import static com.github.javaparser.utils.TestUtils.parseFile;
import static org.junit.jupiter.api.Assertions.assertEquals;

class ExpectedTokensTest {

    @Test
    void testCharEscapeSequences() {
        CompilationUnit compilationUnit = parseFile("/com/github/javaparser/EscapeSequences.java");
        List<CharLiteralExpr> chars = ExtractingVisitors.extractCharLiteralExprs(compilationUnit);
        assertEquals(23, chars.size());

        assertTokenValue(chars, 7, 17, "\\\\");
        assertTokenValue(chars, 7, 23, "\\u005C\\u005C");
        assertTokenValue(chars, 7, 39, "\\u005c\\u005c");
        assertTokenValue(chars, 9, 17, "\\n");
        assertTokenValue(chars, 9, 23, "\\u005cn");
        assertTokenValue(chars, 9, 34, "\\u005Cn");
        assertTokenValue(chars, 11, 17, "\\r");
        assertTokenValue(chars, 11, 23, "\\u005cr");
        assertTokenValue(chars, 11, 34, "\\u005Cr");
        assertTokenValue(chars, 13, 17, "\\t");
        assertTokenValue(chars, 13, 23, "\\u005ct");
        assertTokenValue(chars, 13, 34, "\\u005Ct");
        assertTokenValue(chars, 15, 17, "\\b");
        assertTokenValue(chars, 15, 23, "\\u005cb");
        assertTokenValue(chars, 15, 34, "\\u005Cb");
        assertTokenValue(chars, 17, 17, "\\f");
        assertTokenValue(chars, 17, 23, "\\u005cf");
        assertTokenValue(chars, 17, 34, "\\u005Cf");
        assertTokenValue(chars, 19, 17, "\\'");
        assertTokenValue(chars, 19, 23, "\\u005c'");
        assertTokenValue(chars, 21, 17, "\\\"");
        assertTokenValue(chars, 21, 23, "\\u005c\"");
        assertTokenValue(chars, 21, 34, "\\u005C\"");
    }

    private void assertTokenValue(List<CharLiteralExpr> chars, int line, int col, String expectedTokenValue) {
        CharLiteralExpr expr = getNodeStartingAtPosition(chars, line, col);
        assertEquals(expectedTokenValue, expr.getValue(), "Node at " + line + "," + col);
    }

}
