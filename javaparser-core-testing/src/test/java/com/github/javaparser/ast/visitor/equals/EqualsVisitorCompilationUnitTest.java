/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2024 The JavaParser Team.
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

import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.PackageDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.modules.ModuleDeclaration;
import com.github.javaparser.ast.visitor.EqualsVisitor;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

import java.util.Optional;
import java.util.stream.Stream;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;

class EqualsVisitorCompilationUnitTest extends EqualsVisitorTest
{
    private static final String CODE = "    /**\n" + "    comment\n" + "    **/\n" + "    package a;\n" + "    import java.util.List;\n" + "    public class A {}\n";

    private static final String MODULE = "module com.github.abc { requires a.B; }";

    public static Stream<Arguments> declarationsInScope()
    {
        return Stream.of(Arguments.of(ImportDeclaration.class), Arguments.of(PackageDeclaration.class),
                Arguments.of(ClassOrInterfaceDeclaration.class));
    }

    @Test
    void equals_bothAreNull_true()
    {
        boolean result = EqualsVisitor.equals(null, null);
        assertThat(result, is(true));
    }

    @Test
    void equals_leftIsNull_false()
    {
        parseAndClone(CODE);
        boolean result = EqualsVisitor.equals(null, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_rightIsNull_false()
    {
        parseAndClone(CODE);
        boolean result = EqualsVisitor.equals(nodeLeft, null);
        assertThat(result, is(false));
    }

    @Test
    void equals_rightIsNotCompilationUnit_false(){
        parseAndClone(CODE);
        boolean result = EqualsVisitor.equals(nodeLeft, nodeRight.findFirst(ClassOrInterfaceDeclaration.class).get());
        assertThat(result, is(false));
    }

    @Test
    void equals_sameCode_true()
    {
        parseAndClone(CODE);
        boolean result = EqualsVisitor.equals(nodeLeft, nodeRight);
        assertThat(result, is(true));
    }

    @ParameterizedTest
    @MethodSource("declarationsInScope")
    void equals_differentDeclaration_false(Class<Node> declarationClass)
    {
        parseAndClone(CODE);
        Optional<Node> node = nodeRight.findFirst(declarationClass);
        assertThat("The test code must contain a declaration of type " + declarationClass.getSimpleName() + ".", node.isPresent(),
                is(true));
        node.get().remove();
        boolean result = EqualsVisitor.equals(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_sameModule_true()
    {
        parseAndClone(MODULE);
        boolean result = EqualsVisitor.equals(nodeLeft, nodeRight);
        assertThat(result, is(true));
    }

    @Test
    void equals_differentComment_false()
    {
        parseAndClone(CODE);
        assertThat("The test code must contain a comment at compilation unit level.", nodeRight.getComment().isPresent(), is(true));
        nodeRight.getComment().get().remove();
        boolean result = EqualsVisitor.equals(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentModule_false()
    {
        parseAndClone(MODULE);
        Optional<ModuleDeclaration> node = nodeRight.findFirst(ModuleDeclaration.class);
        assertThat("The test code must contain a module at compilation unit level.", node.isPresent(), is(true));
        node.get().remove();
        boolean result = EqualsVisitor.equals(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }
}