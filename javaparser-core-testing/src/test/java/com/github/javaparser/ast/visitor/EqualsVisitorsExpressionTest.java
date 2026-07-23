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

import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.comments.LineComment;
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
        parseAndClone(CODE);
        nodeRight.findFirst(ArrayAccessExpr.class).get().setIndex(new IntegerLiteralExpr("99"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_arrayAccess_differentName_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(ArrayAccessExpr.class).get().setName(new NameExpr("z"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_arrayAccess_differentComment(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(ArrayAccessExpr.class).get().setComment(new LineComment("changed"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // ArrayCreationExpr tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_arrayCreation_differentElementType_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(ArrayCreationExpr.class).get().setElementType(PrimitiveType.longType());
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_arrayCreation_differentInitializer_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight
                .findFirst(ArrayCreationExpr.class)
                .get()
                .setInitializer(new ArrayInitializerExpr(new NodeList<>(new IntegerLiteralExpr("9"))));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_arrayCreation_differentLevels_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(ArrayCreationExpr.class).get().getLevels().clear();
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_arrayCreation_differentComment(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(ArrayCreationExpr.class).get().setComment(new LineComment("changed"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // ArrayInitializerExpr tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_arrayInitializer_differentValues_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(ArrayInitializerExpr.class).get().getValues().clear();
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_arrayInitializer_differentComment(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(ArrayInitializerExpr.class).get().setComment(new LineComment("changed"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // AssignExpr tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_assign_differentOperator_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(AssignExpr.class).get().setOperator(AssignExpr.Operator.PLUS);
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_assign_differentTarget_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(AssignExpr.class).get().setTarget(new NameExpr("z"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_assign_differentValue_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(AssignExpr.class).get().setValue(new IntegerLiteralExpr("99"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_assign_differentComment(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(AssignExpr.class).get().setComment(new LineComment("changed"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // BinaryExpr tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_binary_differentLeft_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(BinaryExpr.class).get().setLeft(new IntegerLiteralExpr("99"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_binary_differentOperator_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(BinaryExpr.class).get().setOperator(BinaryExpr.Operator.MINUS);
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_binary_differentRight_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(BinaryExpr.class).get().setRight(new IntegerLiteralExpr("99"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_binary_differentComment(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(BinaryExpr.class).get().setComment(new LineComment("changed"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // CastExpr tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_cast_differentExpression_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(CastExpr.class).get().setExpression(new IntegerLiteralExpr("99"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_cast_differentType_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(CastExpr.class).get().setType(PrimitiveType.longType());
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_cast_differentComment(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(CastExpr.class).get().setComment(new LineComment("changed"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // ClassExpr tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_classExpr_differentType_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(ClassExpr.class).get().setType(PrimitiveType.longType());
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_classExpr_differentComment(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(ClassExpr.class).get().setComment(new LineComment("changed"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // ConditionalExpr tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_conditional_differentCondition_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(ConditionalExpr.class).get().setCondition(new BooleanLiteralExpr(false));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_conditional_differentElseExpr_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(ConditionalExpr.class).get().setElseExpr(new IntegerLiteralExpr("99"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_conditional_differentThenExpr_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(ConditionalExpr.class).get().setThenExpr(new IntegerLiteralExpr("99"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_conditional_differentComment(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(ConditionalExpr.class).get().setComment(new LineComment("changed"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // EnclosedExpr tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_enclosed_differentInner_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(EnclosedExpr.class).get().setInner(new IntegerLiteralExpr("99"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_enclosed_differentComment(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(EnclosedExpr.class).get().setComment(new LineComment("changed"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // FieldAccessExpr tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_fieldAccess_differentName_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(FieldAccessExpr.class).get().setName(new SimpleName("other"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_fieldAccess_differentScope_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(FieldAccessExpr.class).get().setScope(new NameExpr("Other"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_fieldAccess_differentTypeArguments_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight
                .findFirst(FieldAccessExpr.class)
                .get()
                .setTypeArguments(new NodeList<>(new ClassOrInterfaceType("String")));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_fieldAccess_differentComment(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(FieldAccessExpr.class).get().setComment(new LineComment("changed"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // InstanceOfExpr tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_instanceOf_differentExpression_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(InstanceOfExpr.class).get().setExpression(new NameExpr("z"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_instanceOf_differentPattern_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight
                .findFirst(InstanceOfExpr.class)
                .get()
                .setPattern(new TypePatternExpr(new NodeList<>(), PrimitiveType.longType(), new SimpleName("x")));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_instanceOf_differentType_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(InstanceOfExpr.class).get().setType(new ClassOrInterfaceType("String"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_instanceOf_differentComment(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(InstanceOfExpr.class).get().setComment(new LineComment("changed"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }
}
