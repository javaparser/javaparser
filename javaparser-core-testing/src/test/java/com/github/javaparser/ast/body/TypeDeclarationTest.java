/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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

package com.github.javaparser.ast.body;

import com.github.javaparser.ast.Node;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.utils.TestParser.parseBodyDeclaration;
import static com.github.javaparser.utils.TestParser.parseCompilationUnit;
import static java.util.stream.Collectors.joining;
import static org.junit.jupiter.api.Assertions.assertEquals;

class TypeDeclarationTest {
    @Test
    void qualifiedNameOfClassInDefaultPackage() {
        assertFQN("X", parseCompilationUnit("class X{ }"));
    }

    @Test
    void qualifiedNameOfClassInAPackage() {
        assertFQN("a.b.c.X", parseCompilationUnit("package a.b.c; class X{}"));
    }

    @Test
    void qualifiedNameOfInterfaceInAPackage() {
        assertFQN("a.b.c.X", parseCompilationUnit("package a.b.c; interface X{}"));
    }

    @Test
    void qualifiedNameOfEnumInAPackage() {
        assertFQN("a.b.c.X", parseCompilationUnit("package a.b.c; enum X{}"));
    }

    @Test
    void qualifiedNameOfAnnotationInAPackage() {
        assertFQN("a.b.c.X", parseCompilationUnit("package a.b.c; @interface X{}"));
    }

    @Test
    void qualifiedNameOfNestedClassInAPackage() {
        assertFQN("a.b.c.Outer,a.b.c.Outer.Nested", parseCompilationUnit("package a.b.c; class Outer{ class Nested {} }"));
    }

    @Test
    void qualifiedNameOfAnonymousClassCantBeQueried() {
        assertFQN("X", parseCompilationUnit("class X{ int aaa() {new Object(){};} }"));
    }

    @Test
    void qualifiedNameOfLocalClassIsEmpty() {
        assertFQN("X,?", parseCompilationUnit("class X{ int aaa() {class Local {}} }"));
    }

    @Test
    void qualifiedNameOfDetachedClassIsEmpty() {
        assertFQN("?", parseBodyDeclaration("class X{}"));
    }

    void assertFQN(String fqn, Node node) {
        assertEquals(fqn, node.findAll(TypeDeclaration.class).stream()
                .map(td -> (TypeDeclaration<?>) td)
                .map(td -> td.getFullyQualifiedName().orElse("?"))
                .collect(joining(",")));
    }
}
