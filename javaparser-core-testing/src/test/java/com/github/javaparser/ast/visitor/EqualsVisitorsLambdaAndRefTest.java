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

import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.SwitchEntry;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.EnumSource;

public class EqualsVisitorsLambdaAndRefTest extends AbstractEqualsVisitorsTest {

    private static final String CODE =
            "class X { Object a = (int x) -> x; Object b = String::valueOf; Object c = switch(1){ case 1 -> 1; default -> 0; }; }";

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_sameLambdaAndRef_true(Strategy strategy) {
        parseAndClone(CODE);
        assertTrue(strategy.areEqual(nodeLeft, nodeRight));
    }

    // LambdaExpr tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_lambda_differentBody_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE, () -> nodeRight.findFirst(LambdaExpr.class).get(), n -> n.setBody(new BlockStmt()), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_lambda_differentEnclosingParameters_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(LambdaExpr.class).get(),
                n -> n.setEnclosingParameters(false),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_lambda_differentParameters_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(LambdaExpr.class).get(),
                n -> n.getParameters().clear(),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_lambda_differentComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(LambdaExpr.class).get(), strategy);
    }

    // MethodReferenceExpr tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_methodRef_differentIdentifier_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(MethodReferenceExpr.class).get(),
                n -> n.setIdentifier("other"),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_methodRef_differentScope_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(MethodReferenceExpr.class).get(),
                n -> n.setScope(new NameExpr("Other")),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_methodRef_differentTypeArguments_false(Strategy strategy) {
        parseAndClone(CODE);
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(MethodReferenceExpr.class).get(),
                n -> n.setTypeArguments(new NodeList<>(new ClassOrInterfaceType("Integer"))),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_methodRef_differentComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(MethodReferenceExpr.class).get(), strategy);
    }

    // TypeExpr tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_typeExpr_differentType_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> (TypeExpr)
                        nodeRight.findFirst(MethodReferenceExpr.class).get().getScope(),
                n -> n.setType(new ClassOrInterfaceType("Integer")),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_typeExpr_differentComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE,
                () -> (TypeExpr)
                        nodeRight.findFirst(MethodReferenceExpr.class).get().getScope(),
                strategy);
    }

    // SwitchExpr tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_switchExpr_differentEntries_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(SwitchExpr.class).get(),
                n -> n.setEntries(new NodeList<>(new SwitchEntry())),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_switchExpr_differentSelector_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(SwitchExpr.class).get(),
                n -> n.setSelector(new IntegerLiteralExpr("99")),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_switchExpr_differentComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(SwitchExpr.class).get(), strategy);
    }
}
