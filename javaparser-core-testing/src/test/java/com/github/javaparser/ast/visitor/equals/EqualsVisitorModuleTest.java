/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2026 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
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
package com.github.javaparser.ast.visitor.equals;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;

import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.modules.*;
import org.junit.jupiter.api.Test;

public class EqualsVisitorModuleTest extends EqualsVisitorTest {

    private static final String CODE =
            "@anno open module com.example { requires transitive java.base; exports com.example to com.other; provides com.example.Spi with com.example.Impl; uses com.example.Spi; opens com.example to com.other; }";

    // ModuleDeclaration tests

    @Test
    void equals_sameModule_true() {
        parseAndClone(CODE);
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(true));
    }

    @Test
    void equals_differentModuleAnnotations_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(ModuleDeclaration.class).get().getAnnotations().clear();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentModuleDirectives_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(ModuleDeclaration.class).get().getDirectives().clear();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentModuleIsOpen_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(ModuleDeclaration.class).get().setOpen(false);
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentModuleName_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(ModuleDeclaration.class).get().setName("com.different");
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentModuleComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        nodeRight.findFirst(ModuleDeclaration.class).get().setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    // ModuleRequiresDirective tests

    @Test
    void equals_differentRequiresModifiers_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(ModuleRequiresDirective.class).get().getModifiers().clear();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentRequiresName_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(ModuleRequiresDirective.class).get().setName("java.logging");
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentRequiresComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        nodeRight.findFirst(ModuleRequiresDirective.class).get().setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    // ModuleExportsDirective tests

    @Test
    void equals_differentExportsModuleNames_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(ModuleExportsDirective.class).get().getModuleNames().clear();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentExportsName_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(ModuleExportsDirective.class).get().setName("com.different");
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentExportsComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        nodeRight.findFirst(ModuleExportsDirective.class).get().setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    // ModuleProvidesDirective tests

    @Test
    void equals_differentProvidesName_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(ModuleProvidesDirective.class).get().setName("com.different.Spi");
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentProvidesWith_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(ModuleProvidesDirective.class).get().getWith().clear();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentProvidesComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        nodeRight.findFirst(ModuleProvidesDirective.class).get().setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    // ModuleUsesDirective tests

    @Test
    void equals_differentUsesName_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(ModuleUsesDirective.class).get().setName("com.different.Spi");
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentUsesComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        nodeRight.findFirst(ModuleUsesDirective.class).get().setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    // ModuleOpensDirective tests

    @Test
    void equals_differentOpensModuleNames_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(ModuleOpensDirective.class).get().getModuleNames().clear();
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentOpensName_false() {
        parseAndClone(CODE);
        nodeRight.findFirst(ModuleOpensDirective.class).get().setName("com.different");
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentOpensComment_false() {
        parseAndClone(CODE);
        org.junit.jupiter.api.Assumptions.assumeTrue(commentsAffectEquality());
        nodeRight.findFirst(ModuleOpensDirective.class).get().setComment(new LineComment("different"));
        boolean result = equalsNodes(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }
}
