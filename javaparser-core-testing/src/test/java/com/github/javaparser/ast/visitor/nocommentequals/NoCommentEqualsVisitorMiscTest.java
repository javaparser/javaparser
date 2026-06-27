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
package com.github.javaparser.ast.visitor.nocommentequals;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.ReceiverParameter;
import com.github.javaparser.ast.stmt.UnparsableStmt;
import com.github.javaparser.ast.visitor.NoCommentEqualsVisitor;
import com.github.javaparser.ast.visitor.Visitable;
import com.github.javaparser.ast.visitor.equals.EqualsVisitorTest;
import org.junit.jupiter.api.Test;

public class NoCommentEqualsVisitorMiscTest extends EqualsVisitorTest {

    @Override
    protected boolean equalsNodes(Node n, Node n2) {
        return NoCommentEqualsVisitor.equals(n, n2);
    }

    private NoCommentEqualsVisitor visitor() throws Exception {
        java.lang.reflect.Field f = NoCommentEqualsVisitor.class.getDeclaredField("SINGLETON");
        f.setAccessible(true);
        return (NoCommentEqualsVisitor) f.get(null);
    }

    @Test
    void visit_unparsableStmt_alwaysTrue() throws Exception {
        UnparsableStmt left = new UnparsableStmt();
        UnparsableStmt right = new UnparsableStmt();
        boolean result = visitor().visit(left, (Visitable) right);
        assertThat(result, is(true));
    }

    @Test
    void visit_receiverParameter_same_true() throws Exception {
        parseAndClone("class Outer { class Inner { Inner(@anno Outer Outer.this){} } }");
        ReceiverParameter left = nodeLeft.findFirst(ReceiverParameter.class).get();
        ReceiverParameter right = nodeRight.findFirst(ReceiverParameter.class).get();
        boolean result = visitor().visit(left, (Visitable) right);
        assertThat(result, is(true));
    }

    @Test
    void visit_receiverParameter_differentAnnotation_false() throws Exception {
        parseAndClone("class Outer { class Inner { Inner(@anno Outer Outer.this){} } }");
        ReceiverParameter left = nodeLeft.findFirst(ReceiverParameter.class).get();
        ReceiverParameter right = nodeRight.findFirst(ReceiverParameter.class).get();
        right.getAnnotations().clear();
        boolean result = visitor().visit(left, (Visitable) right);
        assertThat(result, is(false));
    }

    @Test
    void visit_receiverParameter_differentName_false() throws Exception {
        parseAndClone("class Outer { class Inner { Inner(@anno Outer Outer.this){} } }");
        ReceiverParameter left = nodeLeft.findFirst(ReceiverParameter.class).get();
        ReceiverParameter right = nodeRight.findFirst(ReceiverParameter.class).get();
        right.getName().setIdentifier("Other");
        boolean result = visitor().visit(left, (Visitable) right);
        assertThat(result, is(false));
    }

    @Test
    void visit_receiverParameter_differentType_false() throws Exception {
        parseAndClone("class Outer { class Inner { Inner(@anno Outer Outer.this){} } }");
        ReceiverParameter left = nodeLeft.findFirst(ReceiverParameter.class).get();
        ReceiverParameter right = nodeRight.findFirst(ReceiverParameter.class).get();
        right.setType(new com.github.javaparser.ast.type.ClassOrInterfaceType("Other"));
        boolean result = visitor().visit(left, (Visitable) right);
        assertThat(result, is(false));
    }

    // ConstructorDeclaration

    @Test
    void visit_constructor_same_true() throws Exception {
        parseAndClone("class X { @anno <T> X(int a) throws Exception {} }");
        com.github.javaparser.ast.body.ConstructorDeclaration left = nodeLeft.findFirst(
                        com.github.javaparser.ast.body.ConstructorDeclaration.class)
                .get();
        com.github.javaparser.ast.body.ConstructorDeclaration right = nodeRight
                .findFirst(com.github.javaparser.ast.body.ConstructorDeclaration.class)
                .get();
        boolean result = visitor().visit(left, (Visitable) right);
        assertThat(result, is(true));
    }

    @Test
    void visit_constructor_differentReceiverParameter_false() throws Exception {
        parseAndClone("class X { @anno <T> X(int a) throws Exception {} }");
        com.github.javaparser.ast.body.ConstructorDeclaration left = nodeLeft.findFirst(
                        com.github.javaparser.ast.body.ConstructorDeclaration.class)
                .get();
        com.github.javaparser.ast.body.ConstructorDeclaration right = nodeRight
                .findFirst(com.github.javaparser.ast.body.ConstructorDeclaration.class)
                .get();
        left.setReceiverParameter(new ReceiverParameter(
                new com.github.javaparser.ast.type.ClassOrInterfaceType("X"),
                new com.github.javaparser.ast.expr.Name("X.this")));
        boolean result = visitor().visit(left, (Visitable) right);
        assertThat(result, is(false));
    }

    // Modifier

    @Test
    void visit_modifier_same_true() throws Exception {
        parseAndClone("class X { public int a; }");
        com.github.javaparser.ast.Modifier left =
                nodeLeft.findFirst(com.github.javaparser.ast.Modifier.class).get();
        com.github.javaparser.ast.Modifier right =
                nodeRight.findFirst(com.github.javaparser.ast.Modifier.class).get();
        boolean result = visitor().visit(left, (Visitable) right);
        assertThat(result, is(true));
    }

    @Test
    void visit_modifier_differentKeyword_false() throws Exception {
        parseAndClone("class X { public int a; }");
        com.github.javaparser.ast.Modifier left =
                nodeLeft.findFirst(com.github.javaparser.ast.Modifier.class).get();
        com.github.javaparser.ast.Modifier right =
                nodeRight.findFirst(com.github.javaparser.ast.Modifier.class).get();
        right.setKeyword(com.github.javaparser.ast.Modifier.Keyword.PRIVATE);
        boolean result = visitor().visit(left, (Visitable) right);
        assertThat(result, is(false));
    }
}
