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

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.EnumSource;

public class EqualsVisitorsStatementTest extends AbstractEqualsVisitorsTest {
    private static final String CODE =
            "class X { X(){ this(1); } void m(){ class Local{} record LocalRec(int a){} assert true : \"msg\"; { int i; } label: ; ; System.out.println(); } }";

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_sameStatements_true(Strategy strategy) {
        parseAndClone(CODE);
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertTrue(result);
    }

    // ExplicitConstructorInvocationStmt

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentExplicitConstructorArguments_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight
                        .findFirst(ExplicitConstructorInvocationStmt.class)
                        .get(),
                n -> n.getArguments().clear(),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentExplicitConstructorExpression_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight
                        .findFirst(ExplicitConstructorInvocationStmt.class)
                        .get(),
                n -> n.setExpression(new NameExpr("other")),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentExplicitConstructorIsThis_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight
                        .findFirst(ExplicitConstructorInvocationStmt.class)
                        .get(),
                n -> n.setThis(false),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentExplicitConstructorTypeArguments_false(Strategy strategy) {
        parseAndClone(CODE);
        ExplicitConstructorInvocationStmt stmt =
                nodeRight.findFirst(ExplicitConstructorInvocationStmt.class).get();
        if (stmt.getTypeArguments().isPresent()) {
            stmt.getTypeArguments().get().add(new ClassOrInterfaceType("String"));
        } else {
            stmt.setTypeArguments(new ClassOrInterfaceType("String"));
        }
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentExplicitConstructorComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE,
                () -> nodeRight
                        .findFirst(ExplicitConstructorInvocationStmt.class)
                        .get(),
                strategy);
    }

    // LocalClassDeclarationStmt

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentLocalClassDeclaration_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(LocalClassDeclarationStmt.class).get(),
                n -> n.getClassDeclaration().setName("Different"),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentLocalClassComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(LocalClassDeclarationStmt.class).get(), strategy);
    }

    // LocalRecordDeclarationStmt

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentLocalRecordDeclaration_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(LocalRecordDeclarationStmt.class).get(),
                n -> n.getRecordDeclaration().setName("Different"),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentLocalRecordComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE,
                () -> nodeRight.findFirst(LocalRecordDeclarationStmt.class).get(),
                strategy);
    }

    // AssertStmt

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentAssertCheck_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(AssertStmt.class).get(),
                n -> n.setCheck(new NameExpr("other")),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentAssertMessage_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE, () -> nodeRight.findFirst(AssertStmt.class).get(), n -> n.removeMessage(), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentAssertComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(AssertStmt.class).get(), strategy);
    }

    // BlockStmt

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentBlockStatements_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(BlockStmt.class).get(),
                n -> n.getStatements().clear(),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentBlockComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(BlockStmt.class).get(), strategy);
    }

    // LabeledStmt

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentLabeledLabel_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(LabeledStmt.class).get(),
                n -> n.setLabel(new SimpleName("different")),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentLabeledStatement_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(LabeledStmt.class).get(),
                n -> n.setStatement(new ReturnStmt()),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentLabeledComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(LabeledStmt.class).get(), strategy);
    }

    // EmptyStmt

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentEmptyComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(EmptyStmt.class).get(), strategy);
    }

    // ExpressionStmt

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentExpressionStmtExpression_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(ExpressionStmt.class).get(),
                n -> n.setExpression(new IntegerLiteralExpr("42")),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentExpressionStmtComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(ExpressionStmt.class).get(), strategy);
    }
}
