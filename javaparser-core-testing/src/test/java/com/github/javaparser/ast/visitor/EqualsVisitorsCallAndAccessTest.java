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
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.EnumSource;

public class EqualsVisitorsCallAndAccessTest extends AbstractEqualsVisitorsTest {

    private static final String CODE =
            "class X { void m(){ X.this.toString(); X.super.toString(); Object o = new Object(){}; int x = foo; @anno final int a = -1; } }";

    // MethodCallExpr

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_sameCode_true(Strategy strategy) {
        parseAndClone(CODE);
        assertTrue(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_methodCallExpr_differentArguments_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE, () -> nodeRight.findFirst(MethodCallExpr.class).get(), n -> n.addArgument("1"), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_methodCallExpr_differentName_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE, () -> nodeRight.findFirst(MethodCallExpr.class).get(), n -> n.setName("other"), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_methodCallExpr_differentScope_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE, () -> nodeRight.findFirst(MethodCallExpr.class).get(), n -> n.removeScope(), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_methodCallExpr_differentTypeArguments_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(MethodCallExpr.class).get(),
                n -> n.setTypeArguments(new ClassOrInterfaceType("String")),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_methodCallExpr_differentComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(MethodCallExpr.class).get(), strategy);
    }

    // NameExpr

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_nameExpr_differentName_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE, () -> nodeRight.findFirst(NameExpr.class).get(), n -> n.setName("other"), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_nameExpr_differentComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(NameExpr.class).get(), strategy);
    }

    // ObjectCreationExpr

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_objectCreationExpr_differentAnonymousClassBody_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(ObjectCreationExpr.class).get(),
                n -> n.setAnonymousClassBody(null),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_objectCreationExpr_differentArguments_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE, () -> nodeRight.findFirst(ObjectCreationExpr.class).get(), n -> n.addArgument("1"), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_objectCreationExpr_differentScope_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(ObjectCreationExpr.class).get(),
                n -> n.setScope(new NameExpr("x")),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_objectCreationExpr_differentType_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE, () -> nodeRight.findFirst(ObjectCreationExpr.class).get(), n -> n.setType("String"), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_objectCreationExpr_differentTypeArguments_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(ObjectCreationExpr.class).get(),
                n -> n.setTypeArguments(new ClassOrInterfaceType("String")),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_objectCreationExpr_differentComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(ObjectCreationExpr.class).get(), strategy);
    }

    // Name

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_name_differentIdentifier_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE, () -> nodeRight.findFirst(Name.class).get(), n -> n.setIdentifier("other"), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_name_differentQualifier_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE, () -> nodeRight.findFirst(Name.class).get(), n -> n.setQualifier(new Name("q")), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_name_differentComment(Strategy strategy) {
        assertCommentChangeHandled(CODE, () -> nodeRight.findFirst(Name.class).get(), strategy);
    }

    // SimpleName

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_simpleName_differentIdentifier_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE, () -> nodeRight.findFirst(SimpleName.class).get(), n -> n.setIdentifier("other"), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_simpleName_differentComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(SimpleName.class).get(), strategy);
    }

    // ThisExpr

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_thisExpr_differentTypeName_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE, () -> nodeRight.findFirst(ThisExpr.class).get(), n -> n.setTypeName(new Name("Y")), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_thisExpr_differentComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(ThisExpr.class).get(), strategy);
    }

    // SuperExpr

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_superExpr_differentTypeName_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE, () -> nodeRight.findFirst(SuperExpr.class).get(), n -> n.setTypeName(new Name("Y")), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_superExpr_differentComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(SuperExpr.class).get(), strategy);
    }

    // UnaryExpr

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_unaryExpr_differentExpression_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(UnaryExpr.class).get(),
                n -> n.setExpression(new IntegerLiteralExpr("2")),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_unaryExpr_differentOperator_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(UnaryExpr.class).get(),
                n -> n.setOperator(UnaryExpr.Operator.PLUS),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_unaryExpr_differentComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(UnaryExpr.class).get(), strategy);
    }

    // VariableDeclarationExpr

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_variableDeclarationExpr_differentAnnotations_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findAll(VariableDeclarationExpr.class).get(2),
                n -> n.setAnnotations(new NodeList<>()),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_variableDeclarationExpr_differentModifiers_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findAll(VariableDeclarationExpr.class).get(2),
                n -> n.setModifiers(new NodeList<>()),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_variableDeclarationExpr_differentVariables_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight
                        .findAll(VariableDeclarationExpr.class)
                        .get(2)
                        .getVariables()
                        .get(0),
                n -> n.setName("b"),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_variableDeclarationExpr_differentComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(VariableDeclarationExpr.class).get(), strategy);
    }
}
