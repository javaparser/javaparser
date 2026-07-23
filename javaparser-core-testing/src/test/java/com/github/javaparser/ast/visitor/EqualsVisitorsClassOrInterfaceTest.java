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

import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.expr.SimpleName;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.EnumSource;

public class EqualsVisitorsClassOrInterfaceTest extends AbstractEqualsVisitorsTest {
    private static final String CLASS =
            "@anno public sealed class a <T> extends b implements c permits d{" + "void e(){}" + "}";

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_sameClass_true(Strategy strategy) {
        parseAndClone(CLASS);
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertTrue(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentClass_false(Strategy strategy) {
        parseAndClone(CLASS);
        SimpleName className = getRightClass().getName();
        className.setIdentifier(className.getIdentifier() + ".differentName");
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertFalse(result);
    }

    ClassOrInterfaceDeclaration getRightClass() {
        return nodeRight.getType(0).asClassOrInterfaceDeclaration();
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentClassAnnotation_false(Strategy strategy) {
        parseAndClone(CLASS);
        getRightClass().getAnnotations().remove(0);
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertFalse(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_leftIsClassRightIsInterface_false(Strategy strategy) {
        parseAndClone(CLASS);
        getRightClass().setInterface(true);
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertFalse(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentExtends_false(Strategy strategy) {
        parseAndClone(CLASS);
        getRightClass().getExtendedTypes(0).remove();
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertFalse(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentImplements_false(Strategy strategy) {
        parseAndClone(CLASS);
        getRightClass().getImplementedTypes(0).remove();
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertFalse(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentPermittedTypes_false(Strategy strategy) {
        parseAndClone(CLASS);
        getRightClass().getPermittedTypes().get(0).remove();
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertFalse(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentTypeParameters_false(Strategy strategy) {
        parseAndClone(CLASS);
        getRightClass().getTypeParameters().get(0).remove();
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertFalse(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentMembers_false(Strategy strategy) {
        parseAndClone(CLASS);
        getRightClass().getMembers().remove(0);
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertFalse(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentModifiers_false(Strategy strategy) {
        parseAndClone(CLASS);
        getRightClass().getModifiers().remove(0);
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertFalse(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentCompact_false(Strategy strategy) {
        parseAndClone(CLASS);
        getRightClass().setCompact(!getRightClass().isCompact());
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertFalse(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentClassComment(Strategy strategy) {
        parseAndClone(CLASS);
        getRightClass().setComment(new com.github.javaparser.ast.comments.LineComment("diff"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }
}
