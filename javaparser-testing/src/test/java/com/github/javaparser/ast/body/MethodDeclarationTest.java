package com.github.javaparser.ast.body;

import org.junit.Test;

import static com.github.javaparser.JavaParser.parseClassBodyDeclaration;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;

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

    @Test
    public void signaturesEqual() {
        MethodDeclaration method1 = (MethodDeclaration) parseClassBodyDeclaration("void x(String a) { }");
        MethodDeclaration method2 = (MethodDeclaration) parseClassBodyDeclaration("int x(String z);");
        assertEquals(method1.getSignature(), method2.getSignature());
    }

    @Test
    public void signaturesDifferentName() {
        MethodDeclaration method1 = (MethodDeclaration) parseClassBodyDeclaration("void x(String a) { }");
        MethodDeclaration method2 = (MethodDeclaration) parseClassBodyDeclaration("int y(String z);");
        assertNotEquals(method1.getSignature(), method2.getSignature());
    }

    @Test
    public void signaturesDifferentTypes() {
        MethodDeclaration method1 = (MethodDeclaration) parseClassBodyDeclaration("void x(String a) { }");
        MethodDeclaration method2 = (MethodDeclaration) parseClassBodyDeclaration("int x(int z);");
        assertNotEquals(method1.getSignature(), method2.getSignature());
    }

    @Test
    public void signaturesDifferentVarargs() {
        MethodDeclaration method1 = (MethodDeclaration) parseClassBodyDeclaration("int x(int z);");
        MethodDeclaration method2 = (MethodDeclaration) parseClassBodyDeclaration("int x(int... z);");
        assertNotEquals(method1.getSignature(), method2.getSignature());
    }
}
