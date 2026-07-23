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

import com.github.javaparser.ast.body.FieldDeclaration;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.EnumSource;

public class EqualsVisitorsFieldTest extends AbstractEqualsVisitorsTest {
    private static final String FIELD = "class X { private static @anno int a=15*15; }";

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_sameField_true(Strategy strategy) {
        parseAndClone(FIELD);
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertTrue(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentMember_false(Strategy strategy) {
        parseAndClone(FIELD);
        FieldDeclaration field = getRightField();
        field.getModifiers().clear();
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    FieldDeclaration getRightField() {
        return nodeRight.getType(0).getMember(0).asFieldDeclaration();
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentVariable_false(Strategy strategy) {
        parseAndClone(FIELD);
        FieldDeclaration field = getRightField();
        field.getVariables().clear();
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentAnnotation_false(Strategy strategy) {
        parseAndClone(FIELD);
        FieldDeclaration field = getRightField();
        field.getAnnotations().clear();
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentFieldComment(Strategy strategy) {
        parseAndClone(FIELD);
        getRightField().setComment(new com.github.javaparser.ast.comments.LineComment("diff"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }
}
