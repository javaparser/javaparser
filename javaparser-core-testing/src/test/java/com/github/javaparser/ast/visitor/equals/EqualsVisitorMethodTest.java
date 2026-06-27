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

import com.github.javaparser.ast.body.InitializerDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.type.PrimitiveType;
import org.junit.jupiter.api.Test;

public class EqualsVisitorMethodTest extends EqualsVisitorTest {
    private static final String METHOD = "class X { @anno public <T> int m(int a) throws Exception { return 1; } }";
    private static final String INITIALIZER = "class X { static { int i = 0; } }";

    // --- MethodDeclaration ---

    @Test
    void equals_sameMethod_true() {
        parseAndClone(METHOD);
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(true));
    }

    MethodDeclaration getRightMethod() {
        return nodeRight.getType(0).getMethods().get(0);
    }

    @Test
    void equals_method_differentBody_false() {
        parseAndClone(METHOD);
        getRightMethod().getBody().get().getStatements().clear();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_method_differentType_false() {
        parseAndClone(METHOD);
        getRightMethod().setType(PrimitiveType.booleanType());
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_method_differentModifiers_false() {
        parseAndClone(METHOD);
        getRightMethod().getModifiers().clear();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_method_differentName_false() {
        parseAndClone(METHOD);
        getRightMethod().setName("other");
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_method_differentParameters_false() {
        parseAndClone(METHOD);
        getRightMethod().getParameters().clear();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_method_differentReceiverParameter_false() {
        parseAndClone(METHOD);
        getRightMethod()
                .setReceiverParameter(new com.github.javaparser.ast.body.ReceiverParameter(
                        new com.github.javaparser.ast.type.ClassOrInterfaceType("X"),
                        new com.github.javaparser.ast.expr.Name("X")));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_method_differentThrownExceptions_false() {
        parseAndClone(METHOD);
        getRightMethod().getThrownExceptions().clear();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_method_differentTypeParameters_false() {
        parseAndClone(METHOD);
        getRightMethod().getTypeParameters().clear();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_method_differentAnnotations_false() {
        parseAndClone(METHOD);
        getRightMethod().getAnnotations().clear();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_method_differentComment_false() {
        parseAndClone(METHOD);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        getRightMethod().setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    // --- Parameter ---

    @Test
    void equals_sameParameter_true() {
        parseAndClone(METHOD);
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(true));
    }

    Parameter getRightParameter() {
        return getRightMethod().getParameter(0);
    }

    @Test
    void equals_parameter_differentAnnotations_false() {
        parseAndClone(METHOD);
        getRightParameter().addMarkerAnnotation("Override");
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_parameter_differentIsVarArgs_false() {
        parseAndClone(METHOD);
        getRightParameter().setVarArgs(true);
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_parameter_differentModifiers_false() {
        parseAndClone(METHOD);
        getRightParameter().addModifier(com.github.javaparser.ast.Modifier.Keyword.FINAL);
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_parameter_differentName_false() {
        parseAndClone(METHOD);
        getRightParameter().setName("other");
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_parameter_differentType_false() {
        parseAndClone(METHOD);
        getRightParameter().setType(PrimitiveType.booleanType());
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_parameter_differentVarArgsAnnotations_false() {
        parseAndClone(METHOD);
        getRightParameter().setVarArgs(true);
        getRightParameter()
                .getVarArgsAnnotations()
                .add(new com.github.javaparser.ast.expr.MarkerAnnotationExpr("Nonnull"));
        // Also set left parameter to varargs so only annotations differ
        nodeLeft.getType(0).getMethods().get(0).getParameter(0).setVarArgs(true);
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_parameter_differentComment_false() {
        parseAndClone(METHOD);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        getRightParameter().setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    // --- InitializerDeclaration ---

    @Test
    void equals_sameInitializer_true() {
        parseAndClone(INITIALIZER);
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(true));
    }

    InitializerDeclaration getRightInitializer() {
        return nodeRight.getType(0).findFirst(InitializerDeclaration.class).get();
    }

    @Test
    void equals_initializer_differentBody_false() {
        parseAndClone(INITIALIZER);
        getRightInitializer().getBody().getStatements().clear();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_initializer_differentIsStatic_false() {
        parseAndClone(INITIALIZER);
        getRightInitializer().setStatic(false);
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_initializer_differentAnnotations_false() {
        parseAndClone(INITIALIZER);
        getRightInitializer().addMarkerAnnotation("Override");
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_initializer_differentComment_false() {
        parseAndClone(INITIALIZER);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        getRightInitializer().setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }
}
