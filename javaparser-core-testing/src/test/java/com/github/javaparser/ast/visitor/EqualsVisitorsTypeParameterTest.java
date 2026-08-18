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

import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.type.TypeParameter;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.EnumSource;

public class EqualsVisitorsTypeParameterTest extends AbstractEqualsVisitorsTest {
    private static final String TYPE_PARAMETER = " public class a <@Foo T extends Number> {}";

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_sameTypeParameter_true(Strategy strategy) {
        parseAndClone(TYPE_PARAMETER);
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertTrue(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentTypeParameter_false(Strategy strategy) {
        parseAndClone(TYPE_PARAMETER);
        SimpleName typeParameterName = getRightTypeParameter().getName();
        typeParameterName.setIdentifier(typeParameterName.getIdentifier() + "differentName");
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertFalse(result);
    }

    TypeParameter getRightTypeParameter() {
        return nodeRight.getType(0).asClassOrInterfaceDeclaration().getTypeParameter(0);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentAnnotation_false(Strategy strategy) {
        parseAndClone(TYPE_PARAMETER);
        TypeParameter typeParameter = getRightTypeParameter();
        typeParameter.getAnnotations().clear();
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertFalse(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentBound_false(Strategy strategy) {
        parseAndClone(TYPE_PARAMETER);
        TypeParameter typeParameter = getRightTypeParameter();
        typeParameter.getTypeBound().clear();
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertFalse(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentTypeParameterComment(Strategy strategy) {
        parseAndClone(TYPE_PARAMETER);
        getRightTypeParameter().setComment(new com.github.javaparser.ast.comments.LineComment("diff"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }
}
