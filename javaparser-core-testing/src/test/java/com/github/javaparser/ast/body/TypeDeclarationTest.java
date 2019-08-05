package com.github.javaparser.ast.body;

import com.github.javaparser.ast.CompilationUnit;
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