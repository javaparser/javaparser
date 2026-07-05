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

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.ReceiverParameter;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.comments.MarkdownComment;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.stmt.UnparsableStmt;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.EnumSource;

public class EqualsVisitorsMiscTest extends AbstractEqualsVisitorsTest {

    // ReceiverParameter

    private static final String RECEIVER_CODE = "class Outer { class Inner { Inner(@anno Outer Outer.this){} } }";

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_sameReceiverParameter_true(Strategy strategy) {
        parseAndClone(RECEIVER_CODE);
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertTrue(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentReceiverParameterAnnotation_false(Strategy strategy) {
        parseAndClone(RECEIVER_CODE);
        ReceiverParameter rp = nodeRight.findFirst(ReceiverParameter.class).get();
        rp.getAnnotations().clear();
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentReceiverParameterName_false(Strategy strategy) {
        parseAndClone(RECEIVER_CODE);
        ReceiverParameter rp = nodeRight.findFirst(ReceiverParameter.class).get();
        rp.setName(new Name("Different.this"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentReceiverParameterType_false(Strategy strategy) {
        parseAndClone(RECEIVER_CODE);
        ReceiverParameter rp = nodeRight.findFirst(ReceiverParameter.class).get();
        rp.setType(new ClassOrInterfaceType("String"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentReceiverParameterComment(Strategy strategy) {
        parseAndClone(RECEIVER_CODE);
        ReceiverParameter rp = nodeRight.findFirst(ReceiverParameter.class).get();
        rp.setComment(new LineComment("different"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // Modifier

    private static final String MODIFIER_CODE = "class X { public void m(){} }";

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_sameModifier_true(Strategy strategy) {
        parseAndClone(MODIFIER_CODE);
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertTrue(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentModifierKeyword_false(Strategy strategy) {
        parseAndClone(MODIFIER_CODE);
        Modifier mod = nodeRight.findFirst(Modifier.class).get();
        mod.setKeyword(Modifier.Keyword.PRIVATE);
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentModifierComment(Strategy strategy) {
        parseAndClone(MODIFIER_CODE);
        Modifier mod = nodeRight.findFirst(Modifier.class).get();
        mod.setComment(new LineComment("different"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // NodeList

    private static final String NODELIST_CODE = "class X { void m(int a, int b){} }";

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_sameNodeList_true(Strategy strategy) {
        parseAndClone(NODELIST_CODE);
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertTrue(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentNodeListSize_false(Strategy strategy) {
        parseAndClone(NODELIST_CODE);
        MethodDeclaration md = nodeRight.findFirst(MethodDeclaration.class).get();
        md.getParameters().add(new Parameter(new ClassOrInterfaceType("String"), "c"));
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentNodeListElement_false(Strategy strategy) {
        parseAndClone(NODELIST_CODE);
        MethodDeclaration md = nodeRight.findFirst(MethodDeclaration.class).get();
        md.getParameters().remove(0);
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    // UnparsableStmt

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_sameUnparsableStmt_true(Strategy strategy) {
        UnparsableStmt left = new UnparsableStmt();
        UnparsableStmt right = new UnparsableStmt();
        boolean result = strategy.areEqual(left, right);
        assertTrue(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentUnparsableStmtComment(Strategy strategy) {
        UnparsableStmt left = new UnparsableStmt();
        UnparsableStmt right = new UnparsableStmt();
        right.setComment(new LineComment("different"));
        assertThat(strategy.areEqual(left, right), is(strategy.expectedResultOnDifferentComments()));
    }

    // MarkdownComment

    private static final String MARKDOWN_CODE = "/// markdown comment\nclass X{}";

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_sameMarkdownComment_true(Strategy strategy) {
        parseAndClone(MARKDOWN_CODE);
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertTrue(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentMarkdownCommentContent(Strategy strategy) {
        parseAndClone(MARKDOWN_CODE);
        MarkdownComment mc = (MarkdownComment) nodeRight.getAllComments().stream()
                .filter(c -> c instanceof MarkdownComment)
                .findFirst()
                .get();
        mc.setContent("different content");
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentMarkdownCommentComment(Strategy strategy) {
        parseAndClone(MARKDOWN_CODE);
        nodeRight.getAllComments().stream()
                .filter(c -> c instanceof MarkdownComment)
                .findFirst()
                .get()
                .remove();
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // NodeList visit method

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_nodeListDirectly_true(Strategy strategy) {
        parseAndClone("class X { void a(){} void b(){} }");
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertTrue(result);
    }
}
