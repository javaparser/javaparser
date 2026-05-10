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

package com.github.javaparser.ast.body;

import static com.github.javaparser.utils.TestParser.parseBodyDeclaration;
import static com.github.javaparser.utils.TestParser.parseCompilationUnit;
import static java.util.stream.Collectors.joining;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import org.junit.jupiter.api.Test;

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
        assertFQN(
                "a.b.c.Outer,a.b.c.Outer.Nested",
                parseCompilationUnit("package a.b.c; class Outer{ class Nested {} }"));
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

    /**
     * "module" became a keyword in Java 9, but can still be used as an identifier
     * in certain contexts. This test verifies the AST for an enum named "module"
     * that also uses "module" as a return type and in a field access expression.
     */
    @Test
    void enumWithModuleAsName() {
        String s = "enum module {\n"
                + "  FOO;\n"
                + "\n"
                + "  module foo() {\n"
                + "    return module.FOO;\n"
                + "  }\n"
                + "}\n";

        CompilationUnit cu = parseCompilationUnit(s);

        // Verify there is exactly one enum declaration
        assertEquals(1, cu.findAll(EnumDeclaration.class).size());

        EnumDeclaration enumDecl = cu.findFirst(EnumDeclaration.class).get();
        assertEquals("module", enumDecl.getNameAsString());

        // Verify the enum has one constant "FOO"
        assertEquals(1, enumDecl.getEntries().size());
        EnumConstantDeclaration constant = enumDecl.getEntries().get(0);
        assertEquals("FOO", constant.getNameAsString());

        // Verify the enum has one method "foo"
        assertEquals(1, enumDecl.getMembers().size());
        assertTrue(enumDecl.getMembers().get(0).isMethodDeclaration());

        MethodDeclaration method = enumDecl.getMembers().get(0).asMethodDeclaration();
        assertEquals("foo", method.getNameAsString());

        // Verify the return type is "module"
        assertInstanceOf(ClassOrInterfaceType.class, method.getType());
        assertEquals("module", method.getType().asClassOrInterfaceType().getNameAsString());

        // Verify the method body contains a return statement
        assertTrue(method.getBody().isPresent());
        assertEquals(1, method.getBody().get().getStatements().size());
        assertTrue(method.getBody().get().getStatements().get(0).isReturnStmt());

        ReturnStmt returnStmt = method.getBody().get().getStatements().get(0).asReturnStmt();
        assertTrue(returnStmt.getExpression().isPresent());

        // Verify the return expression is a field access "module.FOO"
        assertTrue(returnStmt.getExpression().get().isFieldAccessExpr());
        assertEquals("module.FOO", returnStmt.getExpression().get().toString());
    }

    void assertFQN(String fqn, Node node) {
        assertEquals(
                fqn,
                node.findAll(TypeDeclaration.class).stream()
                        .map(td -> (TypeDeclaration<?>) td)
                        .map(td -> td.getFullyQualifiedName().orElse("?"))
                        .collect(joining(",")));
    }
}
