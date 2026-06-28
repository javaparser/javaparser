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

import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.PrimitiveType;
import org.junit.jupiter.api.Test;

public class EqualsVisitorExpressionTest extends EqualsVisitorTest {

    private static final String CODE =
            "class X { void m(){ int[] a = new int[]{1,2}; a[0] = 1 + 2; int b = (int)3.0; Class<?> c = int.class; int d = true ? 1 : 0; int e = (1); System.out.println(); boolean f = a instanceof @anno int[]; } }";

    @Test
    void equals_sameExpressions_true() {
        parseAndClone(CODE);
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(true));
    }

    // ArrayAccessExpr tests

    @Test
    void equals_arrayAccess_differentIndex_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(ArrayAccessExpr.class).get().setIndex(new IntegerLiteralExpr("99"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_arrayAccess_differentName_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(ArrayAccessExpr.class).get().setName(new NameExpr("z"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_arrayAccess_differentComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        nodeRight.findFirst(ArrayAccessExpr.class).get().setComment(new LineComment("changed"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    // ArrayCreationExpr tests

    @Test
    void equals_arrayCreation_differentElementType_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(ArrayCreationExpr.class).get().setElementType(PrimitiveType.longType());
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_arrayCreation_differentInitializer_false() {
        parseAndClone(CODE);
        nodeRight
                .findFirst(ArrayCreationExpr.class)
                .get()
                .setInitializer(new ArrayInitializerExpr(new NodeList<>(new IntegerLiteralExpr("9"))));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_arrayCreation_differentLevels_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(ArrayCreationExpr.class).get().getLevels().clear();
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_arrayCreation_differentComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        nodeRight.findFirst(ArrayCreationExpr.class).get().setComment(new LineComment("changed"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    // ArrayInitializerExpr tests

    @Test
    void equals_arrayInitializer_differentValues_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(ArrayInitializerExpr.class).get().getValues().clear();
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_arrayInitializer_differentComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        nodeRight.findFirst(ArrayInitializerExpr.class).get().setComment(new LineComment("changed"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    // AssignExpr tests

    @Test
    void equals_assign_differentOperator_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(AssignExpr.class).get().setOperator(AssignExpr.Operator.PLUS);
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_assign_differentTarget_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(AssignExpr.class).get().setTarget(new NameExpr("z"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_assign_differentValue_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(AssignExpr.class).get().setValue(new IntegerLiteralExpr("99"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_assign_differentComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        nodeRight.findFirst(AssignExpr.class).get().setComment(new LineComment("changed"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    // BinaryExpr tests

    @Test
    void equals_binary_differentLeft_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(BinaryExpr.class).get().setLeft(new IntegerLiteralExpr("99"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_binary_differentOperator_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(BinaryExpr.class).get().setOperator(BinaryExpr.Operator.MINUS);
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_binary_differentRight_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(BinaryExpr.class).get().setRight(new IntegerLiteralExpr("99"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_binary_differentComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        nodeRight.findFirst(BinaryExpr.class).get().setComment(new LineComment("changed"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    // CastExpr tests

    @Test
    void equals_cast_differentExpression_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(CastExpr.class).get().setExpression(new IntegerLiteralExpr("99"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_cast_differentType_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(CastExpr.class).get().setType(PrimitiveType.longType());
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_cast_differentComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        nodeRight.findFirst(CastExpr.class).get().setComment(new LineComment("changed"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    // ClassExpr tests

    @Test
    void equals_classExpr_differentType_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(ClassExpr.class).get().setType(PrimitiveType.longType());
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_classExpr_differentComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        nodeRight.findFirst(ClassExpr.class).get().setComment(new LineComment("changed"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    // ConditionalExpr tests

    @Test
    void equals_conditional_differentCondition_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(ConditionalExpr.class).get().setCondition(new BooleanLiteralExpr(false));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_conditional_differentElseExpr_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(ConditionalExpr.class).get().setElseExpr(new IntegerLiteralExpr("99"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_conditional_differentThenExpr_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(ConditionalExpr.class).get().setThenExpr(new IntegerLiteralExpr("99"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_conditional_differentComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        nodeRight.findFirst(ConditionalExpr.class).get().setComment(new LineComment("changed"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    // EnclosedExpr tests

    @Test
    void equals_enclosed_differentInner_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(EnclosedExpr.class).get().setInner(new IntegerLiteralExpr("99"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_enclosed_differentComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        nodeRight.findFirst(EnclosedExpr.class).get().setComment(new LineComment("changed"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    // FieldAccessExpr tests

    @Test
    void equals_fieldAccess_differentName_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(FieldAccessExpr.class).get().setName(new SimpleName("other"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_fieldAccess_differentScope_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(FieldAccessExpr.class).get().setScope(new NameExpr("Other"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_fieldAccess_differentTypeArguments_false() {
        parseAndClone(CODE);
        nodeRight
                .findFirst(FieldAccessExpr.class)
                .get()
                .setTypeArguments(new NodeList<>(new ClassOrInterfaceType("String")));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_fieldAccess_differentComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        nodeRight.findFirst(FieldAccessExpr.class).get().setComment(new LineComment("changed"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    // InstanceOfExpr tests

    @Test
    void equals_instanceOf_differentExpression_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(InstanceOfExpr.class).get().setExpression(new NameExpr("z"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_instanceOf_differentPattern_false() {
        parseAndClone(CODE);
        nodeRight
                .findFirst(InstanceOfExpr.class)
                .get()
                .setPattern(new TypePatternExpr(new NodeList<>(), PrimitiveType.longType(), new SimpleName("x")));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_instanceOf_differentType_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(InstanceOfExpr.class).get().setType(new ClassOrInterfaceType("String"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_instanceOf_differentComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        nodeRight.findFirst(InstanceOfExpr.class).get().setComment(new LineComment("changed"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }
}
