package com.github.javaparser.ast.body;

import org.junit.Ignore;
import org.junit.Test;

import static com.github.javaparser.JavaParser.parseBodyDeclaration;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;

public class MethodDeclarationTest {
    @Test
    public void annotationsAllowedAfterGenericsAndBeforeReturnType() {
        parseBodyDeclaration("public <T> @Abc String method() {return null;}");
    }

    @Test
    public void annotationsAllowedBeforeGenerics() {
        parseBodyDeclaration("public @Abc <T> String method() {return null;}");
    }

    @Test
    public void explicitReceiverParameters1() {
        MethodDeclaration method = (MethodDeclaration) parseBodyDeclaration("void InnerInner(@mypackage.Anno Source.@mypackage.Anno Inner Source.Inner.this) { }");
        assertEquals("Source.Inner.this", method.getParameter(0).getNameAsString());
    }

    // Ignored this test as for the Checker Framework purposes receiver parameter should only pass receiver annotations
    @Ignore
    @Test
    public void explicitReceiverParameters2() {
        MethodDeclaration method = (MethodDeclaration) parseBodyDeclaration("void x(A this) { }");
        assertEquals("this", method.getParameter(0).getNameAsString());
    }

    @Test
    public void signaturesEqual() {
        MethodDeclaration method1 = (MethodDeclaration) parseBodyDeclaration("void x(String a) { }");
        MethodDeclaration method2 = (MethodDeclaration) parseBodyDeclaration("int x(String z);");
        assertEquals(method1.getSignature(), method2.getSignature());
    }

    @Test
    public void signaturesEqualWhenGenericsDiffer() {
        MethodDeclaration method1 = (MethodDeclaration) parseBodyDeclaration("void x(List<Long> a) { }");
        MethodDeclaration method2 = (MethodDeclaration) parseBodyDeclaration("void x(List<Integer> a) { }");
        assertEquals(method1.getSignature(), method2.getSignature());
    }

    @Test
    public void signaturesEqualWhenAnnotationsDiffer() {
        MethodDeclaration method1 = (MethodDeclaration) parseBodyDeclaration("void x(@A @B List a) { }");
        MethodDeclaration method2 = (MethodDeclaration) parseBodyDeclaration("void x(@C List a) { }");
        assertEquals(method1.getSignature(), method2.getSignature());
    }

    @Test
    public void signaturesDifferentName() {
        MethodDeclaration method1 = (MethodDeclaration) parseBodyDeclaration("void x(String a) { }");
        MethodDeclaration method2 = (MethodDeclaration) parseBodyDeclaration("int y(String z);");
        assertNotEquals(method1.getSignature(), method2.getSignature());
    }

    @Test
    public void signaturesDifferentTypes() {
        MethodDeclaration method1 = (MethodDeclaration) parseBodyDeclaration("void x(String a) { }");
        MethodDeclaration method2 = (MethodDeclaration) parseBodyDeclaration("int x(int z);");
        assertNotEquals(method1.getSignature(), method2.getSignature());
    }

    @Test
    public void signaturesDifferentVarargs() {
        MethodDeclaration method1 = (MethodDeclaration) parseBodyDeclaration("int x(int z);");
        MethodDeclaration method2 = (MethodDeclaration) parseBodyDeclaration("int x(int... z);");
        assertNotEquals(method1.getSignature(), method2.getSignature());
    }

    @Test
    public void signatureToString() {
        MethodDeclaration method1 = (MethodDeclaration) parseBodyDeclaration("int x(int z, String q);");
        assertEquals("x(int, String)", method1.getSignature().toString());
    }
}
