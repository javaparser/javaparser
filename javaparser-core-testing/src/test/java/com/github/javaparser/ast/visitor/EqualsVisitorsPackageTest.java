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

import com.github.javaparser.ast.expr.Name;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.EnumSource;

public class EqualsVisitorsPackageTest extends AbstractEqualsVisitorsTest {
    private static final String PACKAGE = "@anno package com.github.javaparser.ast.visitor.equals;";

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_samePackage_true(Strategy strategy) {
        parseAndClone(PACKAGE);
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertTrue(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentPackage_false(Strategy strategy) {
        parseAndClone(PACKAGE);
        Name packageName = nodeRight.getPackageDeclaration().get().getName();
        packageName.setIdentifier(packageName.getIdentifier() + ".differentName");
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentPackageAnnotation_false(Strategy strategy) {
        parseAndClone(PACKAGE);
        nodeRight.getPackageDeclaration().get().getAnnotations().remove(0);
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentPackageComment(Strategy strategy) {
        parseAndClone(PACKAGE);
        nodeRight.getPackageDeclaration().get().setComment(new com.github.javaparser.ast.comments.LineComment("diff"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }
}
