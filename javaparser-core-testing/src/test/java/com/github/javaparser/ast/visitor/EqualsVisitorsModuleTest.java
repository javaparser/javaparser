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

import static org.junit.jupiter.api.Assertions.assertTrue;

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
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(ModuleDeclaration.class).get(),
                n -> n.getAnnotations().clear(),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentModuleDirectives_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(ModuleDeclaration.class).get(),
                n -> n.getDirectives().clear(),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentModuleIsOpen_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE, () -> nodeRight.findFirst(ModuleDeclaration.class).get(), n -> n.setOpen(false), strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentModuleName_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(ModuleDeclaration.class).get(),
                n -> n.setName("com.different"),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentModuleComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(ModuleDeclaration.class).get(), strategy);
    }

    // ModuleRequiresDirective tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentRequiresModifiers_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(ModuleRequiresDirective.class).get(),
                n -> n.getModifiers().clear(),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentRequiresName_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(ModuleRequiresDirective.class).get(),
                n -> n.setName("java.logging"),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentRequiresComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(ModuleRequiresDirective.class).get(), strategy);
    }

    // ModuleExportsDirective tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentExportsModuleNames_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(ModuleExportsDirective.class).get(),
                n -> n.getModuleNames().clear(),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentExportsName_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(ModuleExportsDirective.class).get(),
                n -> n.setName("com.different"),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentExportsComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(ModuleExportsDirective.class).get(), strategy);
    }

    // ModuleProvidesDirective tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentProvidesName_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(ModuleProvidesDirective.class).get(),
                n -> n.setName("com.different.Spi"),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentProvidesWith_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(ModuleProvidesDirective.class).get(),
                n -> n.getWith().clear(),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentProvidesComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(ModuleProvidesDirective.class).get(), strategy);
    }

    // ModuleUsesDirective tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentUsesName_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(ModuleUsesDirective.class).get(),
                n -> n.setName("com.different.Spi"),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentUsesComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(ModuleUsesDirective.class).get(), strategy);
    }

    // ModuleOpensDirective tests

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentOpensModuleNames_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(ModuleOpensDirective.class).get(),
                n -> n.getModuleNames().clear(),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentOpensName_false(Strategy strategy) {
        assertNotEqualAfterMutation(
                CODE,
                () -> nodeRight.findFirst(ModuleOpensDirective.class).get(),
                n -> n.setName("com.different"),
                strategy);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentOpensComment(Strategy strategy) {
        assertCommentChangeHandled(
                CODE, () -> nodeRight.findFirst(ModuleOpensDirective.class).get(), strategy);
    }
}
