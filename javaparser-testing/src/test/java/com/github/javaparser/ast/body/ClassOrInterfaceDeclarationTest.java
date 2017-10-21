package com.github.javaparser.ast.body;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class ClassOrInterfaceDeclarationTest {
    @Test
    public void staticNestedClass() {
        CompilationUnit cu = JavaParser.parse("class X{static class Y{}}");
        ClassOrInterfaceDeclaration y = cu.getClassByName("X").get().getMembers().get(0).asClassOrInterfaceDeclaration();

        assertEquals(false, y.isInnerClass());
        assertEquals(true, y.isNestedType());
        assertEquals(false, y.isLocalClassDeclaration());
    }

    @Test
    public void nestedInterface() {
        CompilationUnit cu = JavaParser.parse("class X{interface Y{}}");
        ClassOrInterfaceDeclaration y = cu.getClassByName("X").get().getMembers().get(0).asClassOrInterfaceDeclaration();

        assertEquals(false, y.isInnerClass());
        assertEquals(true, y.isNestedType());
        assertEquals(false, y.isLocalClassDeclaration());
    }

    @Test
    public void nonStaticNestedClass() {
        CompilationUnit cu = JavaParser.parse("class X{class Y{}}");
        ClassOrInterfaceDeclaration y = cu.getClassByName("X").get().getMembers().get(0).asClassOrInterfaceDeclaration();

        assertEquals(true, y.isInnerClass());
        assertEquals(true, y.isNestedType());
        assertEquals(false, y.isLocalClassDeclaration());
    }

    @Test
    public void topClass() {
        CompilationUnit cu = JavaParser.parse("class X{}");
        ClassOrInterfaceDeclaration y = cu.getClassByName("X").get();

        assertEquals(false, y.isInnerClass());
        assertEquals(false, y.isNestedType());
        assertEquals(false, y.isLocalClassDeclaration());
    }

    @Test
    public void localClass() {
        MethodDeclaration method= (MethodDeclaration)JavaParser.parseBodyDeclaration("void x(){class X{};}");
        ClassOrInterfaceDeclaration x = method.getChildNodesByType(ClassOrInterfaceDeclaration.class).get(0);

        assertEquals(false, x.isInnerClass());
        assertEquals(false, x.isNestedType());
        assertEquals(true, x.isLocalClassDeclaration());
    }
}
