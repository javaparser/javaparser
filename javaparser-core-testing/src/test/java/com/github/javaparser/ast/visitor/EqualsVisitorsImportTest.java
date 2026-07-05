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

import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.comments.LineComment;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.EnumSource;

public class EqualsVisitorsImportTest extends AbstractEqualsVisitorsTest {
    private static final String IMPORT = "import static java.util.Collections.*;";

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_sameImport_true(Strategy strategy) {
        parseAndClone(IMPORT);
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertTrue(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentName_false(Strategy strategy) {
        parseAndClone(IMPORT);
        ImportDeclaration imp = nodeRight.getImport(0);
        imp.setName("java.util.List");
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentIsAsterisk_false(Strategy strategy) {
        parseAndClone(IMPORT);
        ImportDeclaration imp = nodeRight.getImport(0);
        imp.setAsterisk(false);
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentIsStatic_false(Strategy strategy) {
        parseAndClone(IMPORT);
        ImportDeclaration imp = nodeRight.getImport(0);
        imp.setStatic(false);
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentIsModule_false(Strategy strategy) {
        parseAndClone(IMPORT);
        ImportDeclaration imp = nodeRight.getImport(0);
        imp.setModule(true);
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentComment(Strategy strategy) {
        parseAndClone(IMPORT);
        ImportDeclaration imp = nodeRight.getImport(0);
        imp.setComment(new LineComment("different"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }
}
