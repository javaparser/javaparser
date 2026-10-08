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
import com.github.javaparser.ast.body.Parameter;
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
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(SwitchStmt.class).get(),
                n -> n.getEntries().clear(),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentSwitchSelector_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(SwitchStmt.class).get(),
                n -> n.setSelector(new NameExpr("other")),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentSwitchComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(SwitchStmt.class).get(), strategy);
    }

    // SwitchEntry

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentSwitchEntryGuard_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(SwitchEntry.class).get(),
                n -> n.setGuard(new NameExpr("guard")),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentSwitchEntryIsDefault_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE, () -> nodeRight.findFirst(SwitchEntry.class).get(), n -> n.setDefault(true), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentSwitchEntryLabels_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(SwitchEntry.class).get(),
                n -> n.getLabels().clear(),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentSwitchEntryStatements_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(SwitchEntry.class).get(),
                n -> n.getStatements().clear(),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentSwitchEntryType_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(SwitchEntry.class).get(),
                n -> n.setType(SwitchEntry.Type.BLOCK),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentSwitchEntryComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(SwitchEntry.class).get(), strategy);
    }

    // BreakStmt

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentBreakLabel_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(BreakStmt.class).get(),
                n -> n.setLabel(new SimpleName("other")),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentBreakComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(BreakStmt.class).get(), strategy);
    }

    // ReturnStmt

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentReturnExpression_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(ReturnStmt.class).get(),
                n -> n.setExpression(new IntegerLiteralExpr("99")),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentReturnComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(ReturnStmt.class).get(), strategy);
    }

    // IfStmt

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentIfCondition_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(IfStmt.class).get(),
                n -> n.setCondition(new NameExpr("other")),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentIfElseStmt_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE, () -> nodeRight.findFirst(IfStmt.class).get(), n -> n.removeElseStmt(), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentIfThenStmt_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE, () -> nodeRight.findFirst(IfStmt.class).get(), n -> n.setThenStmt(new EmptyStmt()), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentIfComment(Strategy strategy) {
        assertCommentChangeHandled(CODE, () -> nodeRight.findFirst(IfStmt.class).get(), strategy);
    }

    // WhileStmt

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentWhileBody_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE, () -> nodeRight.findFirst(WhileStmt.class).get(), n -> n.setBody(new EmptyStmt()), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentWhileCondition_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(WhileStmt.class).get(),
                n -> n.setCondition(new NameExpr("other")),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentWhileComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(WhileStmt.class).get(), strategy);
    }

    // ContinueStmt

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentContinueLabel_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(ContinueStmt.class).get(),
                n -> n.setLabel(new SimpleName("other")),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentContinueComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(ContinueStmt.class).get(), strategy);
    }

    // DoStmt

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentDoBody_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE, () -> nodeRight.findFirst(DoStmt.class).get(), n -> n.setBody(new EmptyStmt()), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentDoCondition_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(DoStmt.class).get(),
                n -> n.setCondition(new NameExpr("other")),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentDoComment(Strategy strategy) {
        assertCommentChangeHandled(CODE, () -> nodeRight.findFirst(DoStmt.class).get(), strategy);
    }

    // ForEachStmt

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentForEachBody_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE, () -> nodeRight.findFirst(ForEachStmt.class).get(), n -> n.setBody(new EmptyStmt()), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentForEachIterable_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(ForEachStmt.class).get(),
                n -> n.setIterable(new NameExpr("other")),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentForEachVariable_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(ForEachStmt.class).get(),
                n -> n.getVariableDeclarator().setName("other"),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentForEachComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(ForEachStmt.class).get(), strategy);
    }

    // ForStmt

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentForBody_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE, () -> nodeRight.findFirst(ForStmt.class).get(), n -> n.setBody(new EmptyStmt()), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentForCompare_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(ForStmt.class).get(),
                n -> n.setCompare(new NameExpr("other")),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentForInitialization_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(ForStmt.class).get(),
                n -> n.getInitialization().clear(),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentForUpdate_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(ForStmt.class).get(),
                n -> n.getUpdate().clear(),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentForComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(ForStmt.class).get(), strategy);
    }

    // ThrowStmt

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentThrowExpression_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(ThrowStmt.class).get(),
                n -> n.setExpression(new NameExpr("other")),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentThrowComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(ThrowStmt.class).get(), strategy);
    }

    // SynchronizedStmt

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentSynchronizedBody_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(SynchronizedStmt.class).get(),
                n -> n.setBody(new BlockStmt(new NodeList<>(new EmptyStmt()))),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentSynchronizedExpression_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(SynchronizedStmt.class).get(),
                n -> n.setExpression(new NameExpr("other")),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentSynchronizedComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(SynchronizedStmt.class).get(), strategy);
    }

    // TryStmt

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentTryCatchClauses_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(TryStmt.class).get(),
                n -> n.getCatchClauses().clear(),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentTryFinallyBlock_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE, () -> nodeRight.findFirst(TryStmt.class).get(), n -> n.removeFinallyBlock(), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentTryResources_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(TryStmt.class).get(),
                n -> n.getResources().add(new NameExpr("res")),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentTryBlock_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(TryStmt.class).get(),
                n -> n.setTryBlock(new BlockStmt(new NodeList<>(new EmptyStmt()))),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentTryComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(TryStmt.class).get(), strategy);
    }

    // CatchClause

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentCatchBody_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(CatchClause.class).get(),
                n -> n.setBody(new BlockStmt(new NodeList<>(new EmptyStmt()))),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentCatchParameter_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(CatchClause.class).get(),
                n -> n.setParameter(new Parameter(new ClassOrInterfaceType("RuntimeException"), "ex")),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentCatchComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(CatchClause.class).get(), strategy);
    }

    // YieldStmt

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentYieldExpression_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(YieldStmt.class).get(),
                n -> n.setExpression(new IntegerLiteralExpr("99")),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentYieldComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(YieldStmt.class).get(), strategy);
    }
}
