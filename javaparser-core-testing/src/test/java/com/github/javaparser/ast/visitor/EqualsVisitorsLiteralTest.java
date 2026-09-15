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

import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.ast.expr.*;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.EnumSource;

public class EqualsVisitorsLiteralTest extends AbstractEqualsVisitorsTest {
    private static final String CODE =
            "class X { String a = \"hello\"; int b = 42; long c = 42L; char d = 'x'; double e = 3.14; boolean f = true; Object g = null; String h = \"\"\"\n    text\n    \"\"\"; }";

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentStringLiteral_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE, () -> nodeRight.findFirst(StringLiteralExpr.class).get(), n -> n.setValue("world"), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentIntegerLiteral_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE, () -> nodeRight.findFirst(IntegerLiteralExpr.class).get(), n -> n.setValue("99"), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentLongLiteral_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE, () -> nodeRight.findFirst(LongLiteralExpr.class).get(), n -> n.setValue("99L"), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentCharLiteral_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE, () -> nodeRight.findFirst(CharLiteralExpr.class).get(), n -> n.setValue("y"), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentDoubleLiteral_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE, () -> nodeRight.findFirst(DoubleLiteralExpr.class).get(), n -> n.setValue("9.99"), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentBooleanLiteral_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE, () -> nodeRight.findFirst(BooleanLiteralExpr.class).get(), n -> n.setValue(false), strategy);
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
        assertNotEqualAfterMutation(
                CODE, () -> nodeRight.findFirst(TextBlockLiteralExpr.class).get(), n -> n.setValue("other"), strategy);
    }

    // Comment-difference tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentStringLiteralExprComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(StringLiteralExpr.class).get(), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentIntegerLiteralExprComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(IntegerLiteralExpr.class).get(), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentLongLiteralExprComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(LongLiteralExpr.class).get(), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentCharLiteralExprComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(CharLiteralExpr.class).get(), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentDoubleLiteralExprComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(DoubleLiteralExpr.class).get(), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentBooleanLiteralExprComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(BooleanLiteralExpr.class).get(), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentNullLiteralExprComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(NullLiteralExpr.class).get(), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentTextBlockLiteralExprComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(TextBlockLiteralExpr.class).get(), strategy);
    }
}
