package com.github.javaparser.ast.body;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import org.junit.Test;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class ClassOrInterfaceDeclarationTest {
    @Test
    public void staticNestedClass() {
        CompilationUnit cu = JavaParser.parse("class X{static class Y{}}");
        ClassOrInterfaceDeclaration y = cu.getClassByName("X").get().getMembers().get(0).asClassOrInterfaceDeclaration();

        assertFalse(y.isInnerClass());
        assertTrue(y.isNestedType());
        assertFalse(y.isLocalClassDeclaration());
    }

    @Test
    public void nestedInterface() {
        CompilationUnit cu = JavaParser.parse("class X{interface Y{}}");
        ClassOrInterfaceDeclaration y = cu.getClassByName("X").get().getMembers().get(0).asClassOrInterfaceDeclaration();

        assertFalse(y.isInnerClass());
        assertTrue(y.isNestedType());
        assertFalse(y.isLocalClassDeclaration());
    }

    @Test
    public void nonStaticNestedClass() {
        CompilationUnit cu = JavaParser.parse("class X{class Y{}}");
        ClassOrInterfaceDeclaration y = cu.getClassByName("X").get().getMembers().get(0).asClassOrInterfaceDeclaration();

        assertTrue(y.isInnerClass());
        assertTrue(y.isNestedType());
        assertFalse(y.isLocalClassDeclaration());
    }

    @Test
    public void topClass() {
        CompilationUnit cu = JavaParser.parse("class X{}");
        ClassOrInterfaceDeclaration y = cu.getClassByName("X").get();

        assertFalse(y.isInnerClass());
        assertFalse(y.isNestedType());
        assertFalse(y.isLocalClassDeclaration());
    }

    @Test
    public void localClass() {
        MethodDeclaration method= (MethodDeclaration)JavaParser.parseBodyDeclaration("void x(){class X{};}");
        ClassOrInterfaceDeclaration x = method.findFirst(ClassOrInterfaceDeclaration.class).get();

        assertFalse(x.isInnerClass());
        assertFalse(x.isNestedType());
        assertTrue(x.isLocalClassDeclaration());
    }
}
