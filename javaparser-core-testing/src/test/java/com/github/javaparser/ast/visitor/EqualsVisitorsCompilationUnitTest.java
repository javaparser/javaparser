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
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.PackageDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.modules.ModuleDeclaration;
import java.util.Optional;
import java.util.stream.Stream;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.EnumSource;
import org.junit.jupiter.params.provider.MethodSource;

public class EqualsVisitorsCompilationUnitTest extends AbstractEqualsVisitorsTest {
    private static final String CODE = "    /**\n" + "    comment\n" + "    **/\n" + "    package a;\n"
            + "    import java.util.List;\n" + "    public class A {}\n";

    private static final String MODULE = "module com.github.abc { requires a.B; }";

    public static Stream<Arguments> declarationsInScopeAndStrategies() {
        return Stream.of(Strategy.values()).flatMap(strategy -> Stream.of(
                        ImportDeclaration.class, PackageDeclaration.class, ClassOrInterfaceDeclaration.class)
                .map(declarationClass -> Arguments.of(declarationClass, strategy)));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_bothAreNull_true(Strategy strategy) {
        boolean result = strategy.areEqual(null, null);
        assertTrue(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_leftIsNull_false(Strategy strategy) {
        parseAndClone(CODE);
        boolean result = strategy.areEqual(null, nodeRight);
        assertFalse(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_rightIsNull_false(Strategy strategy) {
        parseAndClone(CODE);
        boolean result = strategy.areEqual(nodeLeft, null);
        assertFalse(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_rightIsNotCompilationUnit_false(Strategy strategy) {
        parseAndClone(CODE);
        boolean result = strategy.areEqual(
                nodeLeft, nodeRight.findFirst(ClassOrInterfaceDeclaration.class).get());
        assertFalse(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_sameCode_true(Strategy strategy) {
        parseAndClone(CODE);
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertTrue(result);
    }

    @ParameterizedTest
    @MethodSource("declarationsInScopeAndStrategies")
    void equals_differentDeclaration_false(Class<Node> declarationClass, Strategy strategy) {
        parseAndClone(CODE);
        Optional<Node> node = nodeRight.findFirst(declarationClass);
        assertThat(
                "The test code must contain a declaration of type " + declarationClass.getSimpleName() + ".",
                node.isPresent(),
                is(true));
        node.get().remove();
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertFalse(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_sameModule_true(Strategy strategy) {
        parseAndClone(MODULE);
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertTrue(result);
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentComment(Strategy strategy) {
        parseAndClone(CODE);
        assertThat(
                "The test code must contain a comment at compilation unit level.",
                nodeRight.getComment().isPresent(),
                is(true));
        nodeRight.getComment().get().remove();
        assertThat(strategy.areEqual(nodeLeft, nodeRight), is(strategy.expectedResultOnDifferentComments()));
    }

    @ParameterizedTest
    @EnumSource(Strategy.class)
    void equals_differentModule_false(Strategy strategy) {
        parseAndClone(MODULE);
        Optional<ModuleDeclaration> node = nodeRight.findFirst(ModuleDeclaration.class);
        assertThat("The test code must contain a module at compilation unit level.", node.isPresent(), is(true));
        node.get().remove();
        boolean result = strategy.areEqual(nodeLeft, nodeRight);
        assertFalse(result);
    }
}
