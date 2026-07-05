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
        parseAndClone(CODE);
        nodeRight.findFirst(LambdaExpr.class).get().setBody(new BlockStmt());
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_lambda_differentEnclosingParameters_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(LambdaExpr.class).get().setEnclosingParameters(false);
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_lambda_differentParameters_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(LambdaExpr.class).get().getParameters().clear();
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_lambda_differentComment(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(LambdaExpr.class).get().setComment(new LineComment("changed"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // MethodReferenceExpr tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_methodRef_differentIdentifier_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(MethodReferenceExpr.class).get().setIdentifier("other");
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_methodRef_differentScope_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(MethodReferenceExpr.class).get().setScope(new NameExpr("Other"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_methodRef_differentTypeArguments_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight
                .findFirst(MethodReferenceExpr.class)
                .get()
                .setTypeArguments(new NodeList<>(new ClassOrInterfaceType("Integer")));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_methodRef_differentComment(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(MethodReferenceExpr.class).get().setComment(new LineComment("changed"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // TypeExpr tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_typeExpr_differentType_false(Strategy strategy) {
        parseAndClone(CODE);
        TypeExpr typeExpr =
                (TypeExpr) nodeRight.findFirst(MethodReferenceExpr.class).get().getScope();
        typeExpr.setType(new ClassOrInterfaceType("Integer"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_typeExpr_differentComment(Strategy strategy) {
        parseAndClone(CODE);
        TypeExpr typeExpr =
                (TypeExpr) nodeRight.findFirst(MethodReferenceExpr.class).get().getScope();
        typeExpr.setComment(new LineComment("changed"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // SwitchExpr tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_switchExpr_differentEntries_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(SwitchExpr.class).get().setEntries(new NodeList<>(new SwitchEntry()));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_switchExpr_differentSelector_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(SwitchExpr.class).get().setSelector(new IntegerLiteralExpr("99"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_switchExpr_differentComment(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(SwitchExpr.class).get().setComment(new LineComment("changed"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }
}
