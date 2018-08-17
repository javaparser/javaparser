package com.github.javaparser.ast.body;

import com.github.javaparser.*;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import org.junit.Test;

import static com.github.javaparser.ParserConfiguration.LanguageLevel.BLEEDING_EDGE;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class ClassOrInterfaceDeclarationTest implements JavaParserSugar {
    @Override
    public <N extends Node> ParseResult<N> parse(ParseStart<N> start, Provider provider) {
        return new JavaParser(new ParserConfiguration().setLanguageLevel(BLEEDING_EDGE)).parse(start, provider);
    }

    @Test
    public void staticNestedClass() {
        CompilationUnit cu = parse("class X{static class Y{}}");
        ClassOrInterfaceDeclaration y = cu.getClassByName("X").get().getMembers().get(0).asClassOrInterfaceDeclaration();

        assertFalse(y.isInnerClass());
        assertTrue(y.isNestedType());
        assertFalse(y.isLocalClassDeclaration());
    }

    @Test
    public void nestedInterface() {
        CompilationUnit cu = parse("class X{interface Y{}}");
        ClassOrInterfaceDeclaration y = cu.getClassByName("X").get().getMembers().get(0).asClassOrInterfaceDeclaration();

        assertFalse(y.isInnerClass());
        assertTrue(y.isNestedType());
        assertFalse(y.isLocalClassDeclaration());
    }

    @Test
    public void nonStaticNestedClass() {
        CompilationUnit cu = parse("class X{class Y{}}");
        ClassOrInterfaceDeclaration y = cu.getClassByName("X").get().getMembers().get(0).asClassOrInterfaceDeclaration();

        assertTrue(y.isInnerClass());
        assertTrue(y.isNestedType());
        assertFalse(y.isLocalClassDeclaration());
    }

    @Test
    public void topClass() {
        CompilationUnit cu = parse("class X{}");
        ClassOrInterfaceDeclaration y = cu.getClassByName("X").get();

        assertFalse(y.isInnerClass());
        assertFalse(y.isNestedType());
        assertFalse(y.isLocalClassDeclaration());
    }

    @Test
    public void localClass() {
        MethodDeclaration method= (MethodDeclaration)parseBodyDeclaration("void x(){class X{};}");
        ClassOrInterfaceDeclaration x = method.findFirst(ClassOrInterfaceDeclaration.class).get();

        assertFalse(x.isInnerClass());
        assertFalse(x.isNestedType());
        assertTrue(x.isLocalClassDeclaration());
    }
}
