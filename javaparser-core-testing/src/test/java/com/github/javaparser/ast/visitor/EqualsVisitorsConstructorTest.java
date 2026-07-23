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

import com.github.javaparser.ast.body.ConstructorDeclaration;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.EnumSource;

public class EqualsVisitorsConstructorTest extends AbstractEqualsVisitorsTest {
    private static final String CONSTRUCTOR = "class X { @anno private <T> X(int a) throws Exception {int i; } }";

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_sameConstructor_true(Strategy strategy) {
        parseAndClone(CONSTRUCTOR);
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertTrue(result);
    }

    ConstructorDeclaration getRightConstructor() {
        return nodeRight.getType(0).getConstructors().get(0);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentBody_false(Strategy strategy) {
        parseAndClone(CONSTRUCTOR);
        ConstructorDeclaration constructor = getRightConstructor();
        constructor.getBody().getStatements().clear();
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentModifier_false(Strategy strategy) {
        parseAndClone(CONSTRUCTOR);
        ConstructorDeclaration constructor = getRightConstructor();
        constructor.getModifiers().clear();
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentName_false(Strategy strategy) {
        parseAndClone(CONSTRUCTOR);
        ConstructorDeclaration constructor = getRightConstructor();
        constructor.setName(constructor.getName() + "differentName");
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentParameters_false(Strategy strategy) {
        parseAndClone(CONSTRUCTOR);
        ConstructorDeclaration constructor = getRightConstructor();
        constructor.getParameters().clear();
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentThrownExceptions_false(Strategy strategy) {
        parseAndClone(CONSTRUCTOR);
        ConstructorDeclaration constructor = getRightConstructor();
        constructor.getThrownExceptions().clear();
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentTypeParameters_false(Strategy strategy) {
        parseAndClone(CONSTRUCTOR);
        ConstructorDeclaration constructor = getRightConstructor();
        constructor.getTypeParameters().clear();
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentAnnotations_false(Strategy strategy) {
        parseAndClone(CONSTRUCTOR);
        ConstructorDeclaration constructor = getRightConstructor();
        constructor.getAnnotations().clear();
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentConstructorComment(Strategy strategy) {
        parseAndClone(CONSTRUCTOR);
        getRightConstructor().setComment(new com.github.javaparser.ast.comments.LineComment("diff"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }
}
