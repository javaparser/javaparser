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
import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.ast.body.EnumDeclaration;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.EnumSource;

public class EqualsVisitorsEnumTest extends AbstractEqualsVisitorsTest {
    private static final String ENUM = "public @anno enum a implements c{@anno B(1){long f;}; int d;}";

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_sameEnum_true(Strategy strategy) {
        parseAndClone(ENUM);
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertTrue(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentEntries_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                ENUM, this::getRightEnum, n -> n.getEntries().clear(), strategy);
    }

    EnumDeclaration getRightEnum() {
        return nodeRight.getType(0).asEnumDeclaration();
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentImplemented_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                ENUM, this::getRightEnum, n -> n.getImplementedTypes().clear(), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentMember_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                ENUM, this::getRightEnum, n -> n.getMembers().clear(), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentModifier_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                ENUM, this::getRightEnum, n -> n.getModifiers().clear(), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentName_false(Strategy strategy) {
        assertNotEqualAfterMutation(ENUM, this::getRightEnum, n -> n.setName(n.getName() + "differentName"), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentAnnotation_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                ENUM, this::getRightEnum, n -> n.getAnnotations().clear(), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentEnumConstantArgument_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                ENUM, () -> getRightEnum().getEntry(0), n -> n.getArguments().clear(), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentEnumConstantBody_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                ENUM, () -> getRightEnum().getEntry(0), n -> n.getClassBody().clear(), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentEnumConstantName_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                ENUM, () -> getRightEnum().getEntry(0), n -> n.setName(n.getName() + "differentName"), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentEnumConstantAnnotation_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                ENUM, () -> getRightEnum().getEntry(0), n -> n.getAnnotations().clear(), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentEnumComment(Strategy strategy) {
        parseAndClone(ENUM);
        getRightEnum().setComment(new com.github.javaparser.ast.comments.LineComment("diff"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentEnumConstantComment(Strategy strategy) {
        parseAndClone(ENUM);
        getRightEnum().getEntry(0).setComment(new com.github.javaparser.ast.comments.LineComment("diff"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }
}
