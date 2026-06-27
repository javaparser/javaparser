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
package com.github.javaparser.ast.visitor.equals;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;

import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.expr.*;
import org.junit.jupiter.api.Test;

public class EqualsVisitorLiteralTest extends EqualsVisitorTest {
    private static final String CODE =
            "class X { String a = \"hello\"; int b = 42; long c = 42L; char d = 'x'; double e = 3.14; boolean f = true; Object g = null; String h = \"\"\"\n    text\n    \"\"\"; }";

    @Test
    void equals_differentStringLiteral_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(StringLiteralExpr.class).get().setValue("world");
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_differentIntegerLiteral_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(IntegerLiteralExpr.class).get().setValue("99");
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_differentLongLiteral_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(LongLiteralExpr.class).get().setValue("99L");
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_differentCharLiteral_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(CharLiteralExpr.class).get().setValue("y");
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_differentDoubleLiteral_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(DoubleLiteralExpr.class).get().setValue("9.99");
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_differentBooleanLiteral_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(BooleanLiteralExpr.class).get().setValue(false);
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_sameNullLiteral_true() {
        parseAndClone(CODE);
        assertThat(equalsNodes(nodeLeft, nodeRight), is(true));
    }

    @Test
    void equals_differentTextBlockLiteral_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(TextBlockLiteralExpr.class).get().setValue("other");
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    // Comment-difference tests

    @Test
    void equals_differentStringLiteralExprComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        nodeRight.findFirst(StringLiteralExpr.class).get().setComment(new LineComment("diff"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentIntegerLiteralExprComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        nodeRight.findFirst(IntegerLiteralExpr.class).get().setComment(new LineComment("diff"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentLongLiteralExprComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        nodeRight.findFirst(LongLiteralExpr.class).get().setComment(new LineComment("diff"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentCharLiteralExprComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        nodeRight.findFirst(CharLiteralExpr.class).get().setComment(new LineComment("diff"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentDoubleLiteralExprComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        nodeRight.findFirst(DoubleLiteralExpr.class).get().setComment(new LineComment("diff"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentBooleanLiteralExprComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        nodeRight.findFirst(BooleanLiteralExpr.class).get().setComment(new LineComment("diff"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentNullLiteralExprComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        nodeRight.findFirst(NullLiteralExpr.class).get().setComment(new LineComment("diff"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentTextBlockLiteralExprComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        nodeRight.findFirst(TextBlockLiteralExpr.class).get().setComment(new LineComment("diff"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }
}
