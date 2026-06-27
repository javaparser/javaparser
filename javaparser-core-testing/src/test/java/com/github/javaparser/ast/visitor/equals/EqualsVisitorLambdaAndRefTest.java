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
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.SwitchEntry;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import org.junit.jupiter.api.Test;

public class EqualsVisitorLambdaAndRefTest extends EqualsVisitorTest {

    private static final String CODE =
            "class X { Object a = (int x) -> x; Object b = String::valueOf; Object c = switch(1){ case 1 -> 1; default -> 0; }; }";

    @Test
    void equals_sameLambdaAndRef_true() {
        parseAndClone(CODE);
        assertThat(equalsNodes(nodeLeft, nodeRight), is(true));
    }

    // LambdaExpr tests

    @Test
    void equals_lambda_differentBody_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(LambdaExpr.class).get().setBody(new BlockStmt());
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_lambda_differentEnclosingParameters_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(LambdaExpr.class).get().setEnclosingParameters(false);
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_lambda_differentParameters_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(LambdaExpr.class).get().getParameters().clear();
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_lambda_differentComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        nodeRight.findFirst(LambdaExpr.class).get().setComment(new LineComment("changed"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    // MethodReferenceExpr tests

    @Test
    void equals_methodRef_differentIdentifier_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(MethodReferenceExpr.class).get().setIdentifier("other");
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_methodRef_differentScope_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(MethodReferenceExpr.class).get().setScope(new NameExpr("Other"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_methodRef_differentTypeArguments_false() {
        parseAndClone(CODE);
        nodeRight
                .findFirst(MethodReferenceExpr.class)
                .get()
                .setTypeArguments(new NodeList<>(new ClassOrInterfaceType("Integer")));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_methodRef_differentComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        nodeRight.findFirst(MethodReferenceExpr.class).get().setComment(new LineComment("changed"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    // TypeExpr tests

    @Test
    void equals_typeExpr_differentType_false() {
        parseAndClone(CODE);
        TypeExpr typeExpr =
                (TypeExpr) nodeRight.findFirst(MethodReferenceExpr.class).get().getScope();
        typeExpr.setType(new ClassOrInterfaceType("Integer"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_typeExpr_differentComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        TypeExpr typeExpr =
                (TypeExpr) nodeRight.findFirst(MethodReferenceExpr.class).get().getScope();
        typeExpr.setComment(new LineComment("changed"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    // SwitchExpr tests

    @Test
    void equals_switchExpr_differentEntries_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(SwitchExpr.class).get().setEntries(new NodeList<>(new SwitchEntry()));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_switchExpr_differentSelector_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(SwitchExpr.class).get().setSelector(new IntegerLiteralExpr("99"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_switchExpr_differentComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        nodeRight.findFirst(SwitchExpr.class).get().setComment(new LineComment("changed"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }
}
