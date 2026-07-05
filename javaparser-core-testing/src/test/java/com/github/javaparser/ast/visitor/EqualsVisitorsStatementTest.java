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
        parseAndClone(CODE);
        ExplicitConstructorInvocationStmt stmt =
                nodeRight.findFirst(ExplicitConstructorInvocationStmt.class).get();
        stmt.getArguments().clear();
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentExplicitConstructorExpression_false(Strategy strategy) {
        parseAndClone(CODE);
        ExplicitConstructorInvocationStmt stmt =
                nodeRight.findFirst(ExplicitConstructorInvocationStmt.class).get();
        stmt.setExpression(new NameExpr("other"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentExplicitConstructorIsThis_false(Strategy strategy) {
        parseAndClone(CODE);
        ExplicitConstructorInvocationStmt stmt =
                nodeRight.findFirst(ExplicitConstructorInvocationStmt.class).get();
        stmt.setThis(false);
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
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
        parseAndClone(CODE);
        ExplicitConstructorInvocationStmt stmt =
                nodeRight.findFirst(ExplicitConstructorInvocationStmt.class).get();
        stmt.setComment(new LineComment("different"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // LocalClassDeclarationStmt

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentLocalClassDeclaration_false(Strategy strategy) {
        parseAndClone(CODE);
        LocalClassDeclarationStmt stmt =
                nodeRight.findFirst(LocalClassDeclarationStmt.class).get();
        stmt.getClassDeclaration().setName("Different");
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentLocalClassComment(Strategy strategy) {
        parseAndClone(CODE);
        LocalClassDeclarationStmt stmt =
                nodeRight.findFirst(LocalClassDeclarationStmt.class).get();
        stmt.setComment(new LineComment("different"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // LocalRecordDeclarationStmt

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentLocalRecordDeclaration_false(Strategy strategy) {
        parseAndClone(CODE);
        LocalRecordDeclarationStmt stmt =
                nodeRight.findFirst(LocalRecordDeclarationStmt.class).get();
        stmt.getRecordDeclaration().setName("Different");
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentLocalRecordComment(Strategy strategy) {
        parseAndClone(CODE);
        LocalRecordDeclarationStmt stmt =
                nodeRight.findFirst(LocalRecordDeclarationStmt.class).get();
        stmt.setComment(new LineComment("different"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // AssertStmt

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentAssertCheck_false(Strategy strategy) {
        parseAndClone(CODE);
        AssertStmt stmt = nodeRight.findFirst(AssertStmt.class).get();
        stmt.setCheck(new NameExpr("other"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentAssertMessage_false(Strategy strategy) {
        parseAndClone(CODE);
        AssertStmt stmt = nodeRight.findFirst(AssertStmt.class).get();
        stmt.removeMessage();
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentAssertComment(Strategy strategy) {
        parseAndClone(CODE);
        AssertStmt stmt = nodeRight.findFirst(AssertStmt.class).get();
        stmt.setComment(new LineComment("different"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // BlockStmt

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentBlockStatements_false(Strategy strategy) {
        parseAndClone(CODE);
        BlockStmt stmt = nodeRight.findFirst(BlockStmt.class).get();
        stmt.getStatements().clear();
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentBlockComment(Strategy strategy) {
        parseAndClone(CODE);
        BlockStmt stmt = nodeRight.findFirst(BlockStmt.class).get();
        stmt.setComment(new LineComment("different"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // LabeledStmt

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentLabeledLabel_false(Strategy strategy) {
        parseAndClone(CODE);
        LabeledStmt stmt = nodeRight.findFirst(LabeledStmt.class).get();
        stmt.setLabel(new SimpleName("different"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentLabeledStatement_false(Strategy strategy) {
        parseAndClone(CODE);
        LabeledStmt stmt = nodeRight.findFirst(LabeledStmt.class).get();
        stmt.setStatement(new ReturnStmt());
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentLabeledComment(Strategy strategy) {
        parseAndClone(CODE);
        LabeledStmt stmt = nodeRight.findFirst(LabeledStmt.class).get();
        stmt.setComment(new LineComment("different"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // EmptyStmt

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentEmptyComment(Strategy strategy) {
        parseAndClone(CODE);
        EmptyStmt stmt = nodeRight.findFirst(EmptyStmt.class).get();
        stmt.setComment(new LineComment("different"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // ExpressionStmt

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentExpressionStmtExpression_false(Strategy strategy) {
        parseAndClone(CODE);
        ExpressionStmt stmt = nodeRight.findFirst(ExpressionStmt.class).get();
        stmt.setExpression(new IntegerLiteralExpr("42"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentExpressionStmtComment(Strategy strategy) {
        parseAndClone(CODE);
        ExpressionStmt stmt = nodeRight.findFirst(ExpressionStmt.class).get();
        stmt.setComment(new LineComment("different"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }
}
