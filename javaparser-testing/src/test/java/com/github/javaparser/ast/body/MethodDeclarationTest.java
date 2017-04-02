package com.github.javaparser.ast.body;

import org.junit.Test;

import static com.github.javaparser.JavaParser.parseClassBodyDeclaration;
import static org.junit.Assert.assertEquals;

public class MethodDeclarationTest {
    @Test
    public void annotationsAllowedAfterGenericsAndBeforeReturnType() {
        parseClassBodyDeclaration("public <T> @Abc String method() {return null;}");
    }

    @Test
    public void annotationsAllowedBeforeGenerics() {
        parseClassBodyDeclaration("public @Abc <T> String method() {return null;}");
    }
    
    @Test
    public void explicitReceiverParameters1() {
        MethodDeclaration method = (MethodDeclaration) parseClassBodyDeclaration("void InnerInner(@mypackage.Anno Source.@mypackage.Anno Inner Source.Inner.this) { }");
        assertEquals("Source.Inner.this", method.getParameter(0).getNameAsString());
    }

    @Test
    public void explicitReceiverParameters2() {
        MethodDeclaration method = (MethodDeclaration) parseClassBodyDeclaration("void x(A this) { }");
        assertEquals("this", method.getParameter(0).getNameAsString());
    }
}
