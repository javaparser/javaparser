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

import com.github.javaparser.ast.expr.CharLiteralExpr;
import com.github.javaparser.ast.expr.DoubleLiteralExpr;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.expr.LongLiteralExpr;
import com.github.javaparser.ast.expr.StringLiteralExpr;
import org.junit.jupiter.api.Test;

/**
 * The typed setters of the literal expressions must notify observers like {@code setValue} does,
 * otherwise the lexical preserving printer keeps printing the old value.
 */
class LiteralValueSettersTest extends AbstractLexicalPreservingTest {

    @Test
    void setString() {
        considerCode("class A { String s = \"a\"; }");
        cu.findFirst(StringLiteralExpr.class).get().setString("b\n");
        assertEqualsStringIgnoringEol("class A { String s = \"b\\n\"; }", LexicalPreservingPrinter.print(cu));
    }

    @Test
    void setEscapedValue() {
        considerCode("class A { String s = \"a\"; }");
        cu.findFirst(StringLiteralExpr.class).get().setEscapedValue("b");
        assertEqualsStringIgnoringEol("class A { String s = \"b\"; }", LexicalPreservingPrinter.print(cu));
    }

    @Test
    void setChar() {
        considerCode("class A { char c = 'a'; }");
        cu.findFirst(CharLiteralExpr.class).get().setChar('b');
        assertEqualsStringIgnoringEol("class A { char c = 'b'; }", LexicalPreservingPrinter.print(cu));
    }

    @Test
    void setDouble() {
        considerCode("class A { double d = 1.0; }");
        cu.findFirst(DoubleLiteralExpr.class).get().setDouble(2.5);
        assertEqualsStringIgnoringEol("class A { double d = 2.5; }", LexicalPreservingPrinter.print(cu));
    }

    @Test
    @SuppressWarnings("deprecation")
    void setInt() {
        considerCode("class A { int i = 1; }");
        cu.findFirst(IntegerLiteralExpr.class).get().setInt(2);
        assertEqualsStringIgnoringEol("class A { int i = 2; }", LexicalPreservingPrinter.print(cu));
    }

    @Test
    @SuppressWarnings("deprecation")
    void setLong() {
        considerCode("class A { long l = 1L; }");
        cu.findFirst(LongLiteralExpr.class).get().setLong(2);
        // The deprecated setLong stores String.valueOf(value) and so drops the L suffix. This test is
        // about the printer seeing the new value; it records that behaviour, it does not endorse it.
        assertEqualsStringIgnoringEol("class A { long l = 2; }", LexicalPreservingPrinter.print(cu));
    }
}
