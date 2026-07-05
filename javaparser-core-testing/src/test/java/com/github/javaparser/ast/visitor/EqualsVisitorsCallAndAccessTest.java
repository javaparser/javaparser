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
        parseAndClone(CODE);
        nodeRight.findFirst(MethodCallExpr.class).get().addArgument("1");
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_methodCallExpr_differentName_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(MethodCallExpr.class).get().setName("other");
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_methodCallExpr_differentScope_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(MethodCallExpr.class).get().removeScope();
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_methodCallExpr_differentTypeArguments_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(MethodCallExpr.class).get().setTypeArguments(new ClassOrInterfaceType("String"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_methodCallExpr_differentComment(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(MethodCallExpr.class).get().setComment(new LineComment("c"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // NameExpr

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_nameExpr_differentName_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(NameExpr.class).get().setName("other");
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_nameExpr_differentComment(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(NameExpr.class).get().setComment(new LineComment("c"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // ObjectCreationExpr

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_objectCreationExpr_differentAnonymousClassBody_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(ObjectCreationExpr.class).get().setAnonymousClassBody(null);
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_objectCreationExpr_differentArguments_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(ObjectCreationExpr.class).get().addArgument("1");
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_objectCreationExpr_differentScope_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(ObjectCreationExpr.class).get().setScope(new NameExpr("x"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_objectCreationExpr_differentType_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(ObjectCreationExpr.class).get().setType("String");
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_objectCreationExpr_differentTypeArguments_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(ObjectCreationExpr.class).get().setTypeArguments(new ClassOrInterfaceType("String"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_objectCreationExpr_differentComment(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(ObjectCreationExpr.class).get().setComment(new LineComment("c"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // Name

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_name_differentIdentifier_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(Name.class).get().setIdentifier("other");
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_name_differentQualifier_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(Name.class).get().setQualifier(new Name("q"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_name_differentComment(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(Name.class).get().setComment(new LineComment("c"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // SimpleName

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_simpleName_differentIdentifier_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(SimpleName.class).get().setIdentifier("other");
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_simpleName_differentComment(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(SimpleName.class).get().setComment(new LineComment("c"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // ThisExpr

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_thisExpr_differentTypeName_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(ThisExpr.class).get().setTypeName(new Name("Y"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_thisExpr_differentComment(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(ThisExpr.class).get().setComment(new LineComment("c"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // SuperExpr

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_superExpr_differentTypeName_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(SuperExpr.class).get().setTypeName(new Name("Y"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_superExpr_differentComment(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(SuperExpr.class).get().setComment(new LineComment("c"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // UnaryExpr

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_unaryExpr_differentExpression_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(UnaryExpr.class).get().setExpression(new IntegerLiteralExpr("2"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_unaryExpr_differentOperator_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(UnaryExpr.class).get().setOperator(UnaryExpr.Operator.PLUS);
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_unaryExpr_differentComment(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(UnaryExpr.class).get().setComment(new LineComment("c"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // VariableDeclarationExpr

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_variableDeclarationExpr_differentAnnotations_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findAll(VariableDeclarationExpr.class).get(2).setAnnotations(new NodeList<>());
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_variableDeclarationExpr_differentModifiers_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findAll(VariableDeclarationExpr.class).get(2).setModifiers(new NodeList<>());
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_variableDeclarationExpr_differentVariables_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight
                .findAll(VariableDeclarationExpr.class)
                .get(2)
                .getVariables()
                .get(0)
                .setName("b");
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_variableDeclarationExpr_differentComment(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(VariableDeclarationExpr.class).get().setComment(new LineComment("c"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }
}
