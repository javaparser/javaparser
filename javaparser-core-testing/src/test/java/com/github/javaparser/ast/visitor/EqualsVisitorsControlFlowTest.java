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
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.EnumSource;

public class EqualsVisitorsControlFlowTest extends AbstractEqualsVisitorsTest {

    private static final String CODE =
            "class X { void m(int x){ switch(x){ case 1: break label; default: } if(true){return 1;}else{} while(true){continue label;} do{}while(true); for(Object o : new int[]{}){} for(int i=0;i<1;i++){} throw new RuntimeException(); synchronized(this){} try{} catch(Exception e){} finally{} } int n(int x){ return switch(x){ case 1: yield 1; default: yield 0; }; } }";

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_sameControlFlow_true(Strategy strategy) {
        parseAndClone(CODE);
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertTrue(result);
    }

    // SwitchStmt

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentSwitchEntries_false(Strategy strategy) {
        parseAndClone(CODE);
        SwitchStmt stmt = nodeRight.findFirst(SwitchStmt.class).get();
        stmt.getEntries().clear();
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentSwitchSelector_false(Strategy strategy) {
        parseAndClone(CODE);
        SwitchStmt stmt = nodeRight.findFirst(SwitchStmt.class).get();
        stmt.setSelector(new NameExpr("other"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentSwitchComment(Strategy strategy) {
        parseAndClone(CODE);
        SwitchStmt stmt = nodeRight.findFirst(SwitchStmt.class).get();
        stmt.setComment(new LineComment("different"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // SwitchEntry

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentSwitchEntryGuard_false(Strategy strategy) {
        parseAndClone(CODE);
        SwitchEntry entry = nodeRight.findFirst(SwitchEntry.class).get();
        entry.setGuard(new NameExpr("guard"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentSwitchEntryIsDefault_false(Strategy strategy) {
        parseAndClone(CODE);
        SwitchEntry entry = nodeRight.findFirst(SwitchEntry.class).get();
        entry.setDefault(true);
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentSwitchEntryLabels_false(Strategy strategy) {
        parseAndClone(CODE);
        SwitchEntry entry = nodeRight.findFirst(SwitchEntry.class).get();
        entry.getLabels().clear();
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentSwitchEntryStatements_false(Strategy strategy) {
        parseAndClone(CODE);
        SwitchEntry entry = nodeRight.findFirst(SwitchEntry.class).get();
        entry.getStatements().clear();
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentSwitchEntryType_false(Strategy strategy) {
        parseAndClone(CODE);
        SwitchEntry entry = nodeRight.findFirst(SwitchEntry.class).get();
        entry.setType(SwitchEntry.Type.BLOCK);
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentSwitchEntryComment(Strategy strategy) {
        parseAndClone(CODE);
        SwitchEntry entry = nodeRight.findFirst(SwitchEntry.class).get();
        entry.setComment(new LineComment("different"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // BreakStmt

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentBreakLabel_false(Strategy strategy) {
        parseAndClone(CODE);
        BreakStmt stmt = nodeRight.findFirst(BreakStmt.class).get();
        stmt.setLabel(new SimpleName("other"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentBreakComment(Strategy strategy) {
        parseAndClone(CODE);
        BreakStmt stmt = nodeRight.findFirst(BreakStmt.class).get();
        stmt.setComment(new LineComment("different"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // ReturnStmt

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentReturnExpression_false(Strategy strategy) {
        parseAndClone(CODE);
        ReturnStmt stmt = nodeRight.findFirst(ReturnStmt.class).get();
        stmt.setExpression(new IntegerLiteralExpr("99"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentReturnComment(Strategy strategy) {
        parseAndClone(CODE);
        ReturnStmt stmt = nodeRight.findFirst(ReturnStmt.class).get();
        stmt.setComment(new LineComment("different"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // IfStmt

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentIfCondition_false(Strategy strategy) {
        parseAndClone(CODE);
        IfStmt stmt = nodeRight.findFirst(IfStmt.class).get();
        stmt.setCondition(new NameExpr("other"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentIfElseStmt_false(Strategy strategy) {
        parseAndClone(CODE);
        IfStmt stmt = nodeRight.findFirst(IfStmt.class).get();
        stmt.removeElseStmt();
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentIfThenStmt_false(Strategy strategy) {
        parseAndClone(CODE);
        IfStmt stmt = nodeRight.findFirst(IfStmt.class).get();
        stmt.setThenStmt(new EmptyStmt());
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentIfComment(Strategy strategy) {
        parseAndClone(CODE);
        IfStmt stmt = nodeRight.findFirst(IfStmt.class).get();
        stmt.setComment(new LineComment("different"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // WhileStmt

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentWhileBody_false(Strategy strategy) {
        parseAndClone(CODE);
        WhileStmt stmt = nodeRight.findFirst(WhileStmt.class).get();
        stmt.setBody(new EmptyStmt());
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentWhileCondition_false(Strategy strategy) {
        parseAndClone(CODE);
        WhileStmt stmt = nodeRight.findFirst(WhileStmt.class).get();
        stmt.setCondition(new NameExpr("other"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentWhileComment(Strategy strategy) {
        parseAndClone(CODE);
        WhileStmt stmt = nodeRight.findFirst(WhileStmt.class).get();
        stmt.setComment(new LineComment("different"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // ContinueStmt

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentContinueLabel_false(Strategy strategy) {
        parseAndClone(CODE);
        ContinueStmt stmt = nodeRight.findFirst(ContinueStmt.class).get();
        stmt.setLabel(new SimpleName("other"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentContinueComment(Strategy strategy) {
        parseAndClone(CODE);
        ContinueStmt stmt = nodeRight.findFirst(ContinueStmt.class).get();
        stmt.setComment(new LineComment("different"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // DoStmt

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentDoBody_false(Strategy strategy) {
        parseAndClone(CODE);
        DoStmt stmt = nodeRight.findFirst(DoStmt.class).get();
        stmt.setBody(new EmptyStmt());
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentDoCondition_false(Strategy strategy) {
        parseAndClone(CODE);
        DoStmt stmt = nodeRight.findFirst(DoStmt.class).get();
        stmt.setCondition(new NameExpr("other"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentDoComment(Strategy strategy) {
        parseAndClone(CODE);
        DoStmt stmt = nodeRight.findFirst(DoStmt.class).get();
        stmt.setComment(new LineComment("different"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // ForEachStmt

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentForEachBody_false(Strategy strategy) {
        parseAndClone(CODE);
        ForEachStmt stmt = nodeRight.findFirst(ForEachStmt.class).get();
        stmt.setBody(new EmptyStmt());
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentForEachIterable_false(Strategy strategy) {
        parseAndClone(CODE);
        ForEachStmt stmt = nodeRight.findFirst(ForEachStmt.class).get();
        stmt.setIterable(new NameExpr("other"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentForEachVariable_false(Strategy strategy) {
        parseAndClone(CODE);
        ForEachStmt stmt = nodeRight.findFirst(ForEachStmt.class).get();
        stmt.getVariableDeclarator().setName("other");
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentForEachComment(Strategy strategy) {
        parseAndClone(CODE);
        ForEachStmt stmt = nodeRight.findFirst(ForEachStmt.class).get();
        stmt.setComment(new LineComment("different"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // ForStmt

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentForBody_false(Strategy strategy) {
        parseAndClone(CODE);
        ForStmt stmt = nodeRight.findFirst(ForStmt.class).get();
        stmt.setBody(new EmptyStmt());
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentForCompare_false(Strategy strategy) {
        parseAndClone(CODE);
        ForStmt stmt = nodeRight.findFirst(ForStmt.class).get();
        stmt.setCompare(new NameExpr("other"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentForInitialization_false(Strategy strategy) {
        parseAndClone(CODE);
        ForStmt stmt = nodeRight.findFirst(ForStmt.class).get();
        stmt.getInitialization().clear();
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentForUpdate_false(Strategy strategy) {
        parseAndClone(CODE);
        ForStmt stmt = nodeRight.findFirst(ForStmt.class).get();
        stmt.getUpdate().clear();
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentForComment(Strategy strategy) {
        parseAndClone(CODE);
        ForStmt stmt = nodeRight.findFirst(ForStmt.class).get();
        stmt.setComment(new LineComment("different"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // ThrowStmt

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentThrowExpression_false(Strategy strategy) {
        parseAndClone(CODE);
        ThrowStmt stmt = nodeRight.findFirst(ThrowStmt.class).get();
        stmt.setExpression(new NameExpr("other"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentThrowComment(Strategy strategy) {
        parseAndClone(CODE);
        ThrowStmt stmt = nodeRight.findFirst(ThrowStmt.class).get();
        stmt.setComment(new LineComment("different"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // SynchronizedStmt

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentSynchronizedBody_false(Strategy strategy) {
        parseAndClone(CODE);
        SynchronizedStmt stmt = nodeRight.findFirst(SynchronizedStmt.class).get();
        stmt.setBody(new BlockStmt(new NodeList<>(new EmptyStmt())));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentSynchronizedExpression_false(Strategy strategy) {
        parseAndClone(CODE);
        SynchronizedStmt stmt = nodeRight.findFirst(SynchronizedStmt.class).get();
        stmt.setExpression(new NameExpr("other"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentSynchronizedComment(Strategy strategy) {
        parseAndClone(CODE);
        SynchronizedStmt stmt = nodeRight.findFirst(SynchronizedStmt.class).get();
        stmt.setComment(new LineComment("different"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // TryStmt

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentTryCatchClauses_false(Strategy strategy) {
        parseAndClone(CODE);
        TryStmt stmt = nodeRight.findFirst(TryStmt.class).get();
        stmt.getCatchClauses().clear();
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentTryFinallyBlock_false(Strategy strategy) {
        parseAndClone(CODE);
        TryStmt stmt = nodeRight.findFirst(TryStmt.class).get();
        stmt.removeFinallyBlock();
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentTryResources_false(Strategy strategy) {
        parseAndClone(CODE);
        TryStmt stmt = nodeRight.findFirst(TryStmt.class).get();
        stmt.getResources().add(new NameExpr("res"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentTryBlock_false(Strategy strategy) {
        parseAndClone(CODE);
        TryStmt stmt = nodeRight.findFirst(TryStmt.class).get();
        stmt.setTryBlock(new BlockStmt(new NodeList<>(new EmptyStmt())));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentTryComment(Strategy strategy) {
        parseAndClone(CODE);
        TryStmt stmt = nodeRight.findFirst(TryStmt.class).get();
        stmt.setComment(new LineComment("different"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // CatchClause

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentCatchBody_false(Strategy strategy) {
        parseAndClone(CODE);
        CatchClause clause = nodeRight.findFirst(CatchClause.class).get();
        clause.setBody(new BlockStmt(new NodeList<>(new EmptyStmt())));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentCatchParameter_false(Strategy strategy) {
        parseAndClone(CODE);
        CatchClause clause = nodeRight.findFirst(CatchClause.class).get();
        clause.setParameter(new Parameter(new ClassOrInterfaceType("RuntimeException"), "ex"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentCatchComment(Strategy strategy) {
        parseAndClone(CODE);
        CatchClause clause = nodeRight.findFirst(CatchClause.class).get();
        clause.setComment(new LineComment("different"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // YieldStmt

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentYieldExpression_false(Strategy strategy) {
        parseAndClone(CODE);
        YieldStmt stmt = nodeRight.findFirst(YieldStmt.class).get();
        stmt.setExpression(new IntegerLiteralExpr("99"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentYieldComment(Strategy strategy) {
        parseAndClone(CODE);
        YieldStmt stmt = nodeRight.findFirst(YieldStmt.class).get();
        stmt.setComment(new LineComment("different"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }
}
