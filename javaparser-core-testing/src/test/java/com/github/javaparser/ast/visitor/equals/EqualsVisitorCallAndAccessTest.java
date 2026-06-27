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
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import org.junit.jupiter.api.Test;

public class EqualsVisitorCallAndAccessTest extends EqualsVisitorTest {

    private static final String CODE =
            "class X { void m(){ X.this.toString(); X.super.toString(); Object o = new Object(){}; int x = foo; @anno final int a = -1; } }";

    // MethodCallExpr

    @Test
    void equals_sameCode_true() {
        parseAndClone(CODE);
        assertThat(equalsNodes(nodeLeft, nodeRight), is(true));
    }

    @Test
    void equals_methodCallExpr_differentArguments_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(MethodCallExpr.class).get().addArgument("1");
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_methodCallExpr_differentName_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(MethodCallExpr.class).get().setName("other");
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_methodCallExpr_differentScope_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(MethodCallExpr.class).get().removeScope();
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_methodCallExpr_differentTypeArguments_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(MethodCallExpr.class).get().setTypeArguments(new ClassOrInterfaceType("String"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_methodCallExpr_differentComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        nodeRight.findFirst(MethodCallExpr.class).get().setComment(new LineComment("c"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    // NameExpr

    @Test
    void equals_nameExpr_differentName_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(NameExpr.class).get().setName("other");
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_nameExpr_differentComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        nodeRight.findFirst(NameExpr.class).get().setComment(new LineComment("c"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    // ObjectCreationExpr

    @Test
    void equals_objectCreationExpr_differentAnonymousClassBody_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(ObjectCreationExpr.class).get().setAnonymousClassBody(null);
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_objectCreationExpr_differentArguments_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(ObjectCreationExpr.class).get().addArgument("1");
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_objectCreationExpr_differentScope_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(ObjectCreationExpr.class).get().setScope(new NameExpr("x"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_objectCreationExpr_differentType_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(ObjectCreationExpr.class).get().setType("String");
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_objectCreationExpr_differentTypeArguments_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(ObjectCreationExpr.class).get().setTypeArguments(new ClassOrInterfaceType("String"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_objectCreationExpr_differentComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        nodeRight.findFirst(ObjectCreationExpr.class).get().setComment(new LineComment("c"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    // Name

    @Test
    void equals_name_differentIdentifier_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(Name.class).get().setIdentifier("other");
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_name_differentQualifier_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(Name.class).get().setQualifier(new Name("q"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_name_differentComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        nodeRight.findFirst(Name.class).get().setComment(new LineComment("c"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    // SimpleName

    @Test
    void equals_simpleName_differentIdentifier_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(SimpleName.class).get().setIdentifier("other");
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_simpleName_differentComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        nodeRight.findFirst(SimpleName.class).get().setComment(new LineComment("c"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    // ThisExpr

    @Test
    void equals_thisExpr_differentTypeName_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(ThisExpr.class).get().setTypeName(new Name("Y"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_thisExpr_differentComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        nodeRight.findFirst(ThisExpr.class).get().setComment(new LineComment("c"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    // SuperExpr

    @Test
    void equals_superExpr_differentTypeName_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(SuperExpr.class).get().setTypeName(new Name("Y"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_superExpr_differentComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        nodeRight.findFirst(SuperExpr.class).get().setComment(new LineComment("c"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    // UnaryExpr

    @Test
    void equals_unaryExpr_differentExpression_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(UnaryExpr.class).get().setExpression(new IntegerLiteralExpr("2"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_unaryExpr_differentOperator_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(UnaryExpr.class).get().setOperator(UnaryExpr.Operator.PLUS);
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_unaryExpr_differentComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        nodeRight.findFirst(UnaryExpr.class).get().setComment(new LineComment("c"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    // VariableDeclarationExpr

    @Test
    void equals_variableDeclarationExpr_differentAnnotations_false() {
        parseAndClone(CODE);
        nodeRight.findAll(VariableDeclarationExpr.class).get(2).setAnnotations(new NodeList<>());
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_variableDeclarationExpr_differentModifiers_false() {
        parseAndClone(CODE);
        nodeRight.findAll(VariableDeclarationExpr.class).get(2).setModifiers(new NodeList<>());
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_variableDeclarationExpr_differentVariables_false() {
        parseAndClone(CODE);
        nodeRight
                .findAll(VariableDeclarationExpr.class)
                .get(2)
                .getVariables()
                .get(0)
                .setName("b");
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }

    @Test
    void equals_variableDeclarationExpr_differentComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        nodeRight.findFirst(VariableDeclarationExpr.class).get().setComment(new LineComment("c"));
        assertThat(equalsNodes(nodeLeft, nodeRight), is(false));
    }
}
