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
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.PrimitiveType;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.EnumSource;

public class EqualsVisitorsExpressionTest extends AbstractEqualsVisitorsTest {

    private static final String CODE =
            "class X { void m(){ int[] a = new int[]{1,2}; a[0] = 1 + 2; int b = (int)3.0; Class<?> c = int.class; int d = true ? 1 : 0; int e = (1); System.out.println(); boolean f = a instanceof @anno int[]; } }";

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_sameExpressions_true(Strategy strategy) {
        parseAndClone(CODE);
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertTrue(result);
    }

    // ArrayAccessExpr tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_arrayAccess_differentIndex_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(ArrayAccessExpr.class).get(),
                n -> n.setIndex(new IntegerLiteralExpr("99")),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_arrayAccess_differentName_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(ArrayAccessExpr.class).get(),
                n -> n.setName(new NameExpr("z")),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_arrayAccess_differentComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(ArrayAccessExpr.class).get(), strategy);
    }

    // ArrayCreationExpr tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_arrayCreation_differentElementType_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(ArrayCreationExpr.class).get(),
                n -> n.setElementType(PrimitiveType.longType()),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_arrayCreation_differentInitializer_false(Strategy strategy) {
        parseAndClone(CODE);
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(ArrayCreationExpr.class).get(),
                n -> n.setInitializer(new ArrayInitializerExpr(new NodeList<>(new IntegerLiteralExpr("9")))),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_arrayCreation_differentLevels_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(ArrayCreationExpr.class).get(),
                n -> n.getLevels().clear(),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_arrayCreation_differentComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(ArrayCreationExpr.class).get(), strategy);
    }

    // ArrayInitializerExpr tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_arrayInitializer_differentValues_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(ArrayInitializerExpr.class).get(),
                n -> n.getValues().clear(),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_arrayInitializer_differentComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(ArrayInitializerExpr.class).get(), strategy);
    }

    // AssignExpr tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_assign_differentOperator_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(AssignExpr.class).get(),
                n -> n.setOperator(AssignExpr.Operator.PLUS),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_assign_differentTarget_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE, () -> nodeRight.findFirst(AssignExpr.class).get(), n -> n.setTarget(new NameExpr("z")), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_assign_differentValue_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(AssignExpr.class).get(),
                n -> n.setValue(new IntegerLiteralExpr("99")),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_assign_differentComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(AssignExpr.class).get(), strategy);
    }

    // BinaryExpr tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_binary_differentLeft_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(BinaryExpr.class).get(),
                n -> n.setLeft(new IntegerLiteralExpr("99")),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_binary_differentOperator_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(BinaryExpr.class).get(),
                n -> n.setOperator(BinaryExpr.Operator.MINUS),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_binary_differentRight_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(BinaryExpr.class).get(),
                n -> n.setRight(new IntegerLiteralExpr("99")),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_binary_differentComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(BinaryExpr.class).get(), strategy);
    }

    // CastExpr tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_cast_differentExpression_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(CastExpr.class).get(),
                n -> n.setExpression(new IntegerLiteralExpr("99")),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_cast_differentType_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(CastExpr.class).get(),
                n -> n.setType(PrimitiveType.longType()),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_cast_differentComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(CastExpr.class).get(), strategy);
    }

    // ClassExpr tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_classExpr_differentType_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(ClassExpr.class).get(),
                n -> n.setType(PrimitiveType.longType()),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_classExpr_differentComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(ClassExpr.class).get(), strategy);
    }

    // ConditionalExpr tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_conditional_differentCondition_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(ConditionalExpr.class).get(),
                n -> n.setCondition(new BooleanLiteralExpr(false)),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_conditional_differentElseExpr_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(ConditionalExpr.class).get(),
                n -> n.setElseExpr(new IntegerLiteralExpr("99")),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_conditional_differentThenExpr_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(ConditionalExpr.class).get(),
                n -> n.setThenExpr(new IntegerLiteralExpr("99")),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_conditional_differentComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(ConditionalExpr.class).get(), strategy);
    }

    // EnclosedExpr tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_enclosed_differentInner_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(EnclosedExpr.class).get(),
                n -> n.setInner(new IntegerLiteralExpr("99")),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_enclosed_differentComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(EnclosedExpr.class).get(), strategy);
    }

    // FieldAccessExpr tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_fieldAccess_differentName_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(FieldAccessExpr.class).get(),
                n -> n.setName(new SimpleName("other")),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_fieldAccess_differentScope_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(FieldAccessExpr.class).get(),
                n -> n.setScope(new NameExpr("Other")),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_fieldAccess_differentTypeArguments_false(Strategy strategy) {
        parseAndClone(CODE);
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(FieldAccessExpr.class).get(),
                n -> n.setTypeArguments(new NodeList<>(new ClassOrInterfaceType("String"))),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_fieldAccess_differentComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(FieldAccessExpr.class).get(), strategy);
    }

    // InstanceOfExpr tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_instanceOf_differentExpression_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(InstanceOfExpr.class).get(),
                n -> n.setExpression(new NameExpr("z")),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_instanceOf_differentPattern_false(Strategy strategy) {
        parseAndClone(CODE);
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(InstanceOfExpr.class).get(),
                n -> n.setPattern(new TypePatternExpr(new NodeList<>(), PrimitiveType.longType(), new SimpleName("x"))),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_instanceOf_differentType_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(InstanceOfExpr.class).get(),
                n -> n.setType(new ClassOrInterfaceType("String")),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_instanceOf_differentComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(InstanceOfExpr.class).get(), strategy);
    }
}
