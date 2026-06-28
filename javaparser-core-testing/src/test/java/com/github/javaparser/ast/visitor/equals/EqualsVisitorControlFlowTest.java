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
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import org.junit.jupiter.api.Test;

public class EqualsVisitorControlFlowTest extends EqualsVisitorTest {

    private static final String CODE =
            "class X { void m(int x){ switch(x){ case 1: break label; default: } if(true){return 1;}else{} while(true){continue label;} do{}while(true); for(Object o : new int[]{}){} for(int i=0;i<1;i++){} throw new RuntimeException(); synchronized(this){} try{} catch(Exception e){} finally{} } int n(int x){ return switch(x){ case 1: yield 1; default: yield 0; }; } }";

    @Test
    void equals_sameControlFlow_true() {
        parseAndClone(CODE);
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(true));
    }

    // SwitchStmt

    @Test
    void equals_differentSwitchEntries_false() {
        parseAndClone(CODE);
        SwitchStmt stmt = nodeRight.findFirst(SwitchStmt.class).get();
        stmt.getEntries().clear();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentSwitchSelector_false() {
        parseAndClone(CODE);
        SwitchStmt stmt = nodeRight.findFirst(SwitchStmt.class).get();
        stmt.setSelector(new NameExpr("other"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentSwitchComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        SwitchStmt stmt = nodeRight.findFirst(SwitchStmt.class).get();
        stmt.setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    // SwitchEntry

    @Test
    void equals_differentSwitchEntryGuard_false() {
        parseAndClone(CODE);
        SwitchEntry entry = nodeRight.findFirst(SwitchEntry.class).get();
        entry.setGuard(new NameExpr("guard"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentSwitchEntryIsDefault_false() {
        parseAndClone(CODE);
        SwitchEntry entry = nodeRight.findFirst(SwitchEntry.class).get();
        entry.setDefault(true);
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentSwitchEntryLabels_false() {
        parseAndClone(CODE);
        SwitchEntry entry = nodeRight.findFirst(SwitchEntry.class).get();
        entry.getLabels().clear();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentSwitchEntryStatements_false() {
        parseAndClone(CODE);
        SwitchEntry entry = nodeRight.findFirst(SwitchEntry.class).get();
        entry.getStatements().clear();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentSwitchEntryType_false() {
        parseAndClone(CODE);
        SwitchEntry entry = nodeRight.findFirst(SwitchEntry.class).get();
        entry.setType(SwitchEntry.Type.BLOCK);
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentSwitchEntryComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        SwitchEntry entry = nodeRight.findFirst(SwitchEntry.class).get();
        entry.setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    // BreakStmt

    @Test
    void equals_differentBreakLabel_false() {
        parseAndClone(CODE);
        BreakStmt stmt = nodeRight.findFirst(BreakStmt.class).get();
        stmt.setLabel(new SimpleName("other"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentBreakComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        BreakStmt stmt = nodeRight.findFirst(BreakStmt.class).get();
        stmt.setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    // ReturnStmt

    @Test
    void equals_differentReturnExpression_false() {
        parseAndClone(CODE);
        ReturnStmt stmt = nodeRight.findFirst(ReturnStmt.class).get();
        stmt.setExpression(new IntegerLiteralExpr("99"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentReturnComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        ReturnStmt stmt = nodeRight.findFirst(ReturnStmt.class).get();
        stmt.setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    // IfStmt

    @Test
    void equals_differentIfCondition_false() {
        parseAndClone(CODE);
        IfStmt stmt = nodeRight.findFirst(IfStmt.class).get();
        stmt.setCondition(new NameExpr("other"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentIfElseStmt_false() {
        parseAndClone(CODE);
        IfStmt stmt = nodeRight.findFirst(IfStmt.class).get();
        stmt.removeElseStmt();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentIfThenStmt_false() {
        parseAndClone(CODE);
        IfStmt stmt = nodeRight.findFirst(IfStmt.class).get();
        stmt.setThenStmt(new EmptyStmt());
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentIfComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        IfStmt stmt = nodeRight.findFirst(IfStmt.class).get();
        stmt.setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    // WhileStmt

    @Test
    void equals_differentWhileBody_false() {
        parseAndClone(CODE);
        WhileStmt stmt = nodeRight.findFirst(WhileStmt.class).get();
        stmt.setBody(new EmptyStmt());
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentWhileCondition_false() {
        parseAndClone(CODE);
        WhileStmt stmt = nodeRight.findFirst(WhileStmt.class).get();
        stmt.setCondition(new NameExpr("other"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentWhileComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        WhileStmt stmt = nodeRight.findFirst(WhileStmt.class).get();
        stmt.setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    // ContinueStmt

    @Test
    void equals_differentContinueLabel_false() {
        parseAndClone(CODE);
        ContinueStmt stmt = nodeRight.findFirst(ContinueStmt.class).get();
        stmt.setLabel(new SimpleName("other"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentContinueComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        ContinueStmt stmt = nodeRight.findFirst(ContinueStmt.class).get();
        stmt.setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    // DoStmt

    @Test
    void equals_differentDoBody_false() {
        parseAndClone(CODE);
        DoStmt stmt = nodeRight.findFirst(DoStmt.class).get();
        stmt.setBody(new EmptyStmt());
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentDoCondition_false() {
        parseAndClone(CODE);
        DoStmt stmt = nodeRight.findFirst(DoStmt.class).get();
        stmt.setCondition(new NameExpr("other"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentDoComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        DoStmt stmt = nodeRight.findFirst(DoStmt.class).get();
        stmt.setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    // ForEachStmt

    @Test
    void equals_differentForEachBody_false() {
        parseAndClone(CODE);
        ForEachStmt stmt = nodeRight.findFirst(ForEachStmt.class).get();
        stmt.setBody(new EmptyStmt());
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentForEachIterable_false() {
        parseAndClone(CODE);
        ForEachStmt stmt = nodeRight.findFirst(ForEachStmt.class).get();
        stmt.setIterable(new NameExpr("other"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentForEachVariable_false() {
        parseAndClone(CODE);
        ForEachStmt stmt = nodeRight.findFirst(ForEachStmt.class).get();
        stmt.getVariableDeclarator().setName("other");
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentForEachComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        ForEachStmt stmt = nodeRight.findFirst(ForEachStmt.class).get();
        stmt.setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    // ForStmt

    @Test
    void equals_differentForBody_false() {
        parseAndClone(CODE);
        ForStmt stmt = nodeRight.findFirst(ForStmt.class).get();
        stmt.setBody(new EmptyStmt());
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentForCompare_false() {
        parseAndClone(CODE);
        ForStmt stmt = nodeRight.findFirst(ForStmt.class).get();
        stmt.setCompare(new NameExpr("other"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentForInitialization_false() {
        parseAndClone(CODE);
        ForStmt stmt = nodeRight.findFirst(ForStmt.class).get();
        stmt.getInitialization().clear();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentForUpdate_false() {
        parseAndClone(CODE);
        ForStmt stmt = nodeRight.findFirst(ForStmt.class).get();
        stmt.getUpdate().clear();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentForComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        ForStmt stmt = nodeRight.findFirst(ForStmt.class).get();
        stmt.setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    // ThrowStmt

    @Test
    void equals_differentThrowExpression_false() {
        parseAndClone(CODE);
        ThrowStmt stmt = nodeRight.findFirst(ThrowStmt.class).get();
        stmt.setExpression(new NameExpr("other"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentThrowComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        ThrowStmt stmt = nodeRight.findFirst(ThrowStmt.class).get();
        stmt.setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    // SynchronizedStmt

    @Test
    void equals_differentSynchronizedBody_false() {
        parseAndClone(CODE);
        SynchronizedStmt stmt = nodeRight.findFirst(SynchronizedStmt.class).get();
        stmt.setBody(new BlockStmt(new NodeList<>(new EmptyStmt())));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentSynchronizedExpression_false() {
        parseAndClone(CODE);
        SynchronizedStmt stmt = nodeRight.findFirst(SynchronizedStmt.class).get();
        stmt.setExpression(new NameExpr("other"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentSynchronizedComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        SynchronizedStmt stmt = nodeRight.findFirst(SynchronizedStmt.class).get();
        stmt.setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    // TryStmt

    @Test
    void equals_differentTryCatchClauses_false() {
        parseAndClone(CODE);
        TryStmt stmt = nodeRight.findFirst(TryStmt.class).get();
        stmt.getCatchClauses().clear();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentTryFinallyBlock_false() {
        parseAndClone(CODE);
        TryStmt stmt = nodeRight.findFirst(TryStmt.class).get();
        stmt.removeFinallyBlock();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentTryResources_false() {
        parseAndClone(CODE);
        TryStmt stmt = nodeRight.findFirst(TryStmt.class).get();
        stmt.getResources().add(new NameExpr("res"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentTryBlock_false() {
        parseAndClone(CODE);
        TryStmt stmt = nodeRight.findFirst(TryStmt.class).get();
        stmt.setTryBlock(new BlockStmt(new NodeList<>(new EmptyStmt())));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentTryComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        TryStmt stmt = nodeRight.findFirst(TryStmt.class).get();
        stmt.setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    // CatchClause

    @Test
    void equals_differentCatchBody_false() {
        parseAndClone(CODE);
        CatchClause clause = nodeRight.findFirst(CatchClause.class).get();
        clause.setBody(new BlockStmt(new NodeList<>(new EmptyStmt())));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentCatchParameter_false() {
        parseAndClone(CODE);
        CatchClause clause = nodeRight.findFirst(CatchClause.class).get();
        clause.setParameter(new Parameter(new ClassOrInterfaceType("RuntimeException"), "ex"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentCatchComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        CatchClause clause = nodeRight.findFirst(CatchClause.class).get();
        clause.setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    // YieldStmt

    @Test
    void equals_differentYieldExpression_false() {
        parseAndClone(CODE);
        YieldStmt stmt = nodeRight.findFirst(YieldStmt.class).get();
        stmt.setExpression(new IntegerLiteralExpr("99"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentYieldComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        YieldStmt stmt = nodeRight.findFirst(YieldStmt.class).get();
        stmt.setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }
}
