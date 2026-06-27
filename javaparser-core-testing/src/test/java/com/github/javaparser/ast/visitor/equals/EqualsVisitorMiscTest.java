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

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.ReceiverParameter;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.comments.MarkdownComment;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.stmt.UnparsableStmt;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.visitor.EqualsVisitor;
import org.junit.jupiter.api.Test;

public class EqualsVisitorMiscTest extends EqualsVisitorTest {

    // ReceiverParameter

    private static final String RECEIVER_CODE = "class Outer { class Inner { Inner(@anno Outer Outer.this){} } }";

    @Test
    void equals_sameReceiverParameter_true() {
        parseAndClone(RECEIVER_CODE);
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(true));
    }

    @Test
    void equals_differentReceiverParameterAnnotation_false() {
        parseAndClone(RECEIVER_CODE);
        ReceiverParameter rp = nodeRight.findFirst(ReceiverParameter.class).get();
        rp.getAnnotations().clear();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentReceiverParameterName_false() {
        parseAndClone(RECEIVER_CODE);
        ReceiverParameter rp = nodeRight.findFirst(ReceiverParameter.class).get();
        rp.setName(new Name("Different.this"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentReceiverParameterType_false() {
        parseAndClone(RECEIVER_CODE);
        ReceiverParameter rp = nodeRight.findFirst(ReceiverParameter.class).get();
        rp.setType(new ClassOrInterfaceType("String"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentReceiverParameterComment_false() {
        parseAndClone(RECEIVER_CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        ReceiverParameter rp = nodeRight.findFirst(ReceiverParameter.class).get();
        rp.setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    // Modifier

    private static final String MODIFIER_CODE = "class X { public void m(){} }";

    @Test
    void equals_sameModifier_true() {
        parseAndClone(MODIFIER_CODE);
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(true));
    }

    @Test
    void equals_differentModifierKeyword_false() {
        parseAndClone(MODIFIER_CODE);
        Modifier mod = nodeRight.findFirst(Modifier.class).get();
        mod.setKeyword(Modifier.Keyword.PRIVATE);
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentModifierComment_false() {
        parseAndClone(MODIFIER_CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        Modifier mod = nodeRight.findFirst(Modifier.class).get();
        mod.setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    // NodeList

    private static final String NODELIST_CODE = "class X { void m(int a, int b){} }";

    @Test
    void equals_sameNodeList_true() {
        parseAndClone(NODELIST_CODE);
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(true));
    }

    @Test
    void equals_differentNodeListSize_false() {
        parseAndClone(NODELIST_CODE);
        MethodDeclaration md = nodeRight.findFirst(MethodDeclaration.class).get();
        md.getParameters().add(new Parameter(new ClassOrInterfaceType("String"), "c"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentNodeListElement_false() {
        parseAndClone(NODELIST_CODE);
        MethodDeclaration md = nodeRight.findFirst(MethodDeclaration.class).get();
        md.getParameters().remove(0);
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    // UnparsableStmt

    @Test
    void equals_sameUnparsableStmt_true() {
        UnparsableStmt left = new UnparsableStmt();
        UnparsableStmt right = new UnparsableStmt();
        boolean result = equalsNodes(left, right);
        assertThat(result, is(true));
    }

    @Test
    void equals_differentUnparsableStmtComment_false() {
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        UnparsableStmt left = new UnparsableStmt();
        UnparsableStmt right = new UnparsableStmt();
        right.setComment(new LineComment("different"));
        boolean result = equalsNodes(left, right);
        assertThat(result, is(false));
    }

    // MarkdownComment

    private static final String MARKDOWN_CODE = "/// markdown comment\nclass X{}";

    @Test
    void equals_sameMarkdownComment_true() {
        parseAndClone(MARKDOWN_CODE);
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(true));
    }

    @Test
    void equals_differentMarkdownCommentContent_false() {
        parseAndClone(MARKDOWN_CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        MarkdownComment mc = (MarkdownComment) nodeRight.getAllComments().stream()
                .filter(c -> c instanceof MarkdownComment)
                .findFirst()
                .get();
        mc.setContent("different content");
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentMarkdownCommentComment_false() {
        parseAndClone(MARKDOWN_CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        // Comments cannot have comments themselves, so we test by removing the comment entirely
        nodeRight.getAllComments().stream()
                .filter(c -> c instanceof MarkdownComment)
                .findFirst()
                .get()
                .remove();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    // NodeList visit method

    @Test
    void equals_nodeListDirectly_true() throws Exception {
        parseAndClone("class X { void a(){} void b(){} }");
        java.lang.reflect.Field f = EqualsVisitor.class.getDeclaredField("SINGLETON");
        f.setAccessible(true);
        EqualsVisitor visitor = (EqualsVisitor) f.get(null);
        NodeList<?> left = nodeLeft.getType(0).asClassOrInterfaceDeclaration().getMembers();
        NodeList<?> right = nodeRight.getType(0).asClassOrInterfaceDeclaration().getMembers();
        @SuppressWarnings("unchecked")
        boolean result = (Boolean) ((NodeList) left).accept(visitor, right);
        assertThat(result, is(true));
    }
}
