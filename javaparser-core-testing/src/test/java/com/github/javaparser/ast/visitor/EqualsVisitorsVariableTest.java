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

import com.github.javaparser.ast.body.VariableDeclarator;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.EnumSource;

public class EqualsVisitorsVariableTest extends AbstractEqualsVisitorsTest {
    private static final String VARIABLE = "class a{ void b(){int a=15;}} ";

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_sameVariable_true(Strategy strategy) {
        parseAndClone(VARIABLE);
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertTrue(result);
    }

    VariableDeclarator getRightVariable() {
        return nodeRight.findFirst(VariableDeclarator.class).get();
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentInitializer_false(Strategy strategy) {
        parseAndClone(VARIABLE);
        VariableDeclarator variable = getRightVariable();
        variable.setInitializer("16");
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertFalse(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentName_false(Strategy strategy) {
        parseAndClone(VARIABLE);
        VariableDeclarator variable = getRightVariable();
        variable.setName(variable.getName() + "differentName");
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertFalse(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentType_false(Strategy strategy) {
        parseAndClone(VARIABLE);
        VariableDeclarator variable = getRightVariable();
        variable.setType("long");
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertFalse(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentVariableComment(Strategy strategy) {
        parseAndClone(VARIABLE);
        getRightVariable().setComment(new com.github.javaparser.ast.comments.LineComment("diff"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }
}
