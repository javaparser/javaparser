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

import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import org.junit.jupiter.api.Test;

public class EqualsVisitorStatementTest extends EqualsVisitorTest {
    private static final String CODE =
            "class X { X(){ this(1); } void m(){ class Local{} record LocalRec(int a){} assert true : \"msg\"; { int i; } label: ; ; System.out.println(); } }";

    @Test
    void equals_sameStatements_true() {
        parseAndClone(CODE);
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(true));
    }

    // ExplicitConstructorInvocationStmt

    @Test
    void equals_differentExplicitConstructorArguments_false() {
        parseAndClone(CODE);
        ExplicitConstructorInvocationStmt stmt =
                nodeRight.findFirst(ExplicitConstructorInvocationStmt.class).get();
        stmt.getArguments().clear();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentExplicitConstructorExpression_false() {
        parseAndClone(CODE);
        ExplicitConstructorInvocationStmt stmt =
                nodeRight.findFirst(ExplicitConstructorInvocationStmt.class).get();
        stmt.setExpression(new NameExpr("other"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentExplicitConstructorIsThis_false() {
        parseAndClone(CODE);
        ExplicitConstructorInvocationStmt stmt =
                nodeRight.findFirst(ExplicitConstructorInvocationStmt.class).get();
        stmt.setThis(false);
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentExplicitConstructorTypeArguments_false() {
        parseAndClone(CODE);
        ExplicitConstructorInvocationStmt stmt =
                nodeRight.findFirst(ExplicitConstructorInvocationStmt.class).get();
        if (stmt.getTypeArguments().isPresent()) {
            stmt.getTypeArguments().get().add(new ClassOrInterfaceType("String"));
        } else {
            stmt.setTypeArguments(new ClassOrInterfaceType("String"));
        }
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentExplicitConstructorComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        ExplicitConstructorInvocationStmt stmt =
                nodeRight.findFirst(ExplicitConstructorInvocationStmt.class).get();
        stmt.setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    // LocalClassDeclarationStmt

    @Test
    void equals_differentLocalClassDeclaration_false() {
        parseAndClone(CODE);
        LocalClassDeclarationStmt stmt =
                nodeRight.findFirst(LocalClassDeclarationStmt.class).get();
        stmt.getClassDeclaration().setName("Different");
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentLocalClassComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        LocalClassDeclarationStmt stmt =
                nodeRight.findFirst(LocalClassDeclarationStmt.class).get();
        stmt.setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    // LocalRecordDeclarationStmt

    @Test
    void equals_differentLocalRecordDeclaration_false() {
        parseAndClone(CODE);
        LocalRecordDeclarationStmt stmt =
                nodeRight.findFirst(LocalRecordDeclarationStmt.class).get();
        stmt.getRecordDeclaration().setName("Different");
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentLocalRecordComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        LocalRecordDeclarationStmt stmt =
                nodeRight.findFirst(LocalRecordDeclarationStmt.class).get();
        stmt.setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    // AssertStmt

    @Test
    void equals_differentAssertCheck_false() {
        parseAndClone(CODE);
        AssertStmt stmt = nodeRight.findFirst(AssertStmt.class).get();
        stmt.setCheck(new NameExpr("other"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentAssertMessage_false() {
        parseAndClone(CODE);
        AssertStmt stmt = nodeRight.findFirst(AssertStmt.class).get();
        stmt.removeMessage();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentAssertComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        AssertStmt stmt = nodeRight.findFirst(AssertStmt.class).get();
        stmt.setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    // BlockStmt

    @Test
    void equals_differentBlockStatements_false() {
        parseAndClone(CODE);
        BlockStmt stmt = nodeRight.findFirst(BlockStmt.class).get();
        stmt.getStatements().clear();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentBlockComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        BlockStmt stmt = nodeRight.findFirst(BlockStmt.class).get();
        stmt.setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    // LabeledStmt

    @Test
    void equals_differentLabeledLabel_false() {
        parseAndClone(CODE);
        LabeledStmt stmt = nodeRight.findFirst(LabeledStmt.class).get();
        stmt.setLabel(new SimpleName("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentLabeledStatement_false() {
        parseAndClone(CODE);
        LabeledStmt stmt = nodeRight.findFirst(LabeledStmt.class).get();
        stmt.setStatement(new ReturnStmt());
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentLabeledComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        LabeledStmt stmt = nodeRight.findFirst(LabeledStmt.class).get();
        stmt.setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    // EmptyStmt

    @Test
    void equals_differentEmptyComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        EmptyStmt stmt = nodeRight.findFirst(EmptyStmt.class).get();
        stmt.setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    // ExpressionStmt

    @Test
    void equals_differentExpressionStmtExpression_false() {
        parseAndClone(CODE);
        ExpressionStmt stmt = nodeRight.findFirst(ExpressionStmt.class).get();
        stmt.setExpression(new IntegerLiteralExpr("42"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentExpressionStmtComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        ExpressionStmt stmt = nodeRight.findFirst(ExpressionStmt.class).get();
        stmt.setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }
}
