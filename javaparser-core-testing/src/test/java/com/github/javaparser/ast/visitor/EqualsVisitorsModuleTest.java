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

import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.modules.*;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.EnumSource;

public class EqualsVisitorsModuleTest extends AbstractEqualsVisitorsTest {

    private static final String CODE =
            "@anno open module com.example { requires transitive java.base; exports com.example to com.other; provides com.example.Spi with com.example.Impl; uses com.example.Spi; opens com.example to com.other; }";

    // ModuleDeclaration tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_sameModule_true(Strategy strategy) {
        parseAndClone(CODE);
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertTrue(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentModuleAnnotations_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(ModuleDeclaration.class).get().getAnnotations().clear();
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentModuleDirectives_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(ModuleDeclaration.class).get().getDirectives().clear();
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentModuleIsOpen_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(ModuleDeclaration.class).get().setOpen(false);
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentModuleName_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(ModuleDeclaration.class).get().setName("com.different");
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentModuleComment(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(ModuleDeclaration.class).get().setComment(new LineComment("different"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // ModuleRequiresDirective tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentRequiresModifiers_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(ModuleRequiresDirective.class).get().getModifiers().clear();
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentRequiresName_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(ModuleRequiresDirective.class).get().setName("java.logging");
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentRequiresComment(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(ModuleRequiresDirective.class).get().setComment(new LineComment("different"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // ModuleExportsDirective tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentExportsModuleNames_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(ModuleExportsDirective.class).get().getModuleNames().clear();
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentExportsName_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(ModuleExportsDirective.class).get().setName("com.different");
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentExportsComment(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(ModuleExportsDirective.class).get().setComment(new LineComment("different"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // ModuleProvidesDirective tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentProvidesName_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(ModuleProvidesDirective.class).get().setName("com.different.Spi");
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentProvidesWith_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(ModuleProvidesDirective.class).get().getWith().clear();
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentProvidesComment(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(ModuleProvidesDirective.class).get().setComment(new LineComment("different"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // ModuleUsesDirective tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentUsesName_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(ModuleUsesDirective.class).get().setName("com.different.Spi");
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentUsesComment(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(ModuleUsesDirective.class).get().setComment(new LineComment("different"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    // ModuleOpensDirective tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentOpensModuleNames_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(ModuleOpensDirective.class).get().getModuleNames().clear();
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentOpensName_false(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(ModuleOpensDirective.class).get().setName("com.different");
        assertFalse(strategy.areEqual(nodeLeft, nodeRight));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentOpensComment(Strategy strategy) {
        parseAndClone(CODE);
        nodeRight.findFirst(ModuleOpensDirective.class).get().setComment(new LineComment("different"));
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }
}
