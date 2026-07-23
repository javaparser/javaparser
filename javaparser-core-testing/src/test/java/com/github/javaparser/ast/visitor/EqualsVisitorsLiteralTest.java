/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2026 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
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
package com.github.javaparser.ast.visitor;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.expr.*;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.EnumSource;

public class EqualsVisitorsLiteralTest extends AbstractEqualsVisitorsTest {
    private static final String CODE =
            "class X { String a = \"hello\"; int b = 42; long c = 42L; char d = 'x'; double e = 3.14; boolean f = true; Object g = null; String h = \"\"\"\n    text\n    \"\"\"; }";

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentStringLiteral_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(StringLiteralExpr.class).get().setValue("world");
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentIntegerLiteral_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(IntegerLiteralExpr.class).get().setValue("99");
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentLongLiteral_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(LongLiteralExpr.class).get().setValue("99L");
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentCharLiteral_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(CharLiteralExpr.class).get().setValue("y");
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentDoubleLiteral_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(DoubleLiteralExpr.class).get().setValue("9.99");
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentBooleanLiteral_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(BooleanLiteralExpr.class).get().setValue(false);
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_sameNullLiteral_true(Strategy strategy) {
        parseAndClone(CODE);
        assertTrue(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentTextBlockLiteral_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(TextBlockLiteralExpr.class).get().setValue("other");
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    // Comment-difference tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentStringLiteralExprComment(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(StringLiteralExpr.class).get().setComment(new LineComment("diff"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentIntegerLiteralExprComment(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(IntegerLiteralExpr.class).get().setComment(new LineComment("diff"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentLongLiteralExprComment(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(LongLiteralExpr.class).get().setComment(new LineComment("diff"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentCharLiteralExprComment(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(CharLiteralExpr.class).get().setComment(new LineComment("diff"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentDoubleLiteralExprComment(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(DoubleLiteralExpr.class).get().setComment(new LineComment("diff"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentBooleanLiteralExprComment(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(BooleanLiteralExpr.class).get().setComment(new LineComment("diff"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentNullLiteralExprComment(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(NullLiteralExpr.class).get().setComment(new LineComment("diff"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentTextBlockLiteralExprComment(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(TextBlockLiteralExpr.class).get().setComment(new LineComment("diff"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }
}
