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

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.ast.body.InitializerDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.type.PrimitiveType;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.EnumSource;

public class EqualsVisitorsMethodTest extends AbstractEqualsVisitorsTest {
    private static final String METHOD = "class X { @anno public <T> int m(int a) throws Exception { return 1; } }";
    private static final String INITIALIZER = "class X { static { int i = 0; } }";

    // --- MethodDeclaration ---

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_sameMethod_true(Strategy strategy) {
        parseAndClone(METHOD);
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertTrue(result);
    }

    MethodDeclaration getRightMethod() {
        return nodeRight.getType(0).getMethods().get(0);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_method_differentBody_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                METHOD,
                this::getRightMethod,
                n -> n.getBody().get().getStatements().clear(),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_method_differentType_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                METHOD, this::getRightMethod, n -> n.setType(PrimitiveType.booleanType()), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_method_differentModifiers_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                METHOD, this::getRightMethod, n -> n.getModifiers().clear(), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_method_differentName_false(Strategy strategy) {
        assertNotEqualAfterMutation(METHOD, this::getRightMethod, n -> n.setName("other"), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_method_differentParameters_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                METHOD, this::getRightMethod, n -> n.getParameters().clear(), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_method_differentReceiverParameter_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                METHOD,
                this::getRightMethod,
                n -> n.setReceiverParameter(new com.github.javaparser.ast.body.ReceiverParameter(
                        new com.github.javaparser.ast.type.ClassOrInterfaceType("X"),
                        new com.github.javaparser.ast.expr.Name("X"))),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_method_differentThrownExceptions_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                METHOD, this::getRightMethod, n -> n.getThrownExceptions().clear(), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_method_differentTypeParameters_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                METHOD, this::getRightMethod, n -> n.getTypeParameters().clear(), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_method_differentAnnotations_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                METHOD, this::getRightMethod, n -> n.getAnnotations().clear(), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_method_differentComment(Strategy strategy) {
        assertCommentChangeHandled(METHOD, () -> getRightMethod(), strategy);
    }

    // --- Parameter ---

    Parameter getRightParameter() {
        return getRightMethod().getParameter(0);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_parameter_differentAnnotations_false(Strategy strategy) {
        assertNotEqualAfterMutation(METHOD, this::getRightParameter, n -> n.addMarkerAnnotation("Override"), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_parameter_differentIsVarArgs_false(Strategy strategy) {
        assertNotEqualAfterMutation(METHOD, this::getRightParameter, n -> n.setVarArgs(true), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_parameter_differentModifiers_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                METHOD,
                this::getRightParameter,
                n -> n.addModifier(com.github.javaparser.ast.Modifier.Keyword.FINAL),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_parameter_differentName_false(Strategy strategy) {
        assertNotEqualAfterMutation(METHOD, this::getRightParameter, n -> n.setName("other"), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_parameter_differentType_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                METHOD, this::getRightParameter, n -> n.setType(PrimitiveType.booleanType()), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_parameter_differentVarArgsAnnotations_false(Strategy strategy) {
        parseAndClone(METHOD);
        getRightParameter().setVarArgs(true);
        getRightParameter()
                .getVarArgsAnnotations()
                .add(new com.github.javaparser.ast.expr.MarkerAnnotationExpr("Nonnull"));
        // Also set left parameter to varargs so only annotations differ
        nodeLeft.getType(0).getMethods().get(0).getParameter(0).setVarArgs(true);
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_parameter_differentComment(Strategy strategy) {
        assertCommentChangeHandled(METHOD, () -> getRightParameter(), strategy);
    }

    // --- InitializerDeclaration ---

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_sameInitializer_true(Strategy strategy) {
        parseAndClone(INITIALIZER);
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertTrue(result);
    }

    InitializerDeclaration getRightInitializer() {
        return nodeRight.getType(0).findFirst(InitializerDeclaration.class).get();
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_initializer_differentBody_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                INITIALIZER,
                this::getRightInitializer,
                n -> n.getBody().getStatements().clear(),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_initializer_differentIsStatic_false(Strategy strategy) {
        assertNotEqualAfterMutation(INITIALIZER, this::getRightInitializer, n -> n.setStatic(false), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_initializer_differentAnnotations_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                INITIALIZER, this::getRightInitializer, n -> n.addMarkerAnnotation("Override"), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_initializer_differentComment(Strategy strategy) {
        assertCommentChangeHandled(INITIALIZER, () -> getRightInitializer(), strategy);
    }
}
