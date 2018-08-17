package com.github.javaparser.ast.body;

import org.junit.Ignore;
import org.junit.Test;

import static com.github.javaparser.JavaParser.parseBodyDeclaration;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
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
        MethodDeclaration method = parseBodyDeclaration("void InnerInner(@mypackage.Anno Source.@mypackage.Anno Inner Source.Inner.this) { }").asMethodDeclaration();
        assertEquals("Source.Inner.this", method.getReceiverParameter().get().getNameAsString());
    }

    @Test
    public void explicitReceiverParameters2() {
        MethodDeclaration method = parseBodyDeclaration("void x(A this) { }").asMethodDeclaration();
        assertEquals("this", method.getReceiverParameter().get().getNameAsString());
    }

    @Test
    public void explicitReceiverParameters3() {
        MethodDeclaration method = parseBodyDeclaration("void x(A that) { }").asMethodDeclaration();
        assertFalse(method.getReceiverParameter().isPresent());
    }

    @Test
    public void signaturesEqual() {
        MethodDeclaration method1 = parseBodyDeclaration("void x(String a) { }").asMethodDeclaration();
        MethodDeclaration method2 = parseBodyDeclaration("int x(String z);").asMethodDeclaration();
        assertEquals(method1.getSignature(), method2.getSignature());
    }

    @Test
    public void signaturesEqualWhenGenericsDiffer() {
        MethodDeclaration method1 = parseBodyDeclaration("void x(List<Long> a) { }").asMethodDeclaration();
        MethodDeclaration method2 = parseBodyDeclaration("void x(List<Integer> a) { }").asMethodDeclaration();
        assertEquals(method1.getSignature(), method2.getSignature());
    }

    @Test
    public void signaturesEqualWhenAnnotationsDiffer() {
        MethodDeclaration method1 = parseBodyDeclaration("void x(@A @B List a) { }").asMethodDeclaration();
        MethodDeclaration method2 = parseBodyDeclaration("void x(@C List a) { }").asMethodDeclaration();
        assertEquals(method1.getSignature(), method2.getSignature());
    }

    @Test
    public void signaturesDifferentName() {
        MethodDeclaration method1 = parseBodyDeclaration("void x(String a) { }").asMethodDeclaration();
        MethodDeclaration method2 = parseBodyDeclaration("int y(String z);").asMethodDeclaration();
        assertNotEquals(method1.getSignature(), method2.getSignature());
    }

    @Test
    public void signaturesDifferentTypes() {
        MethodDeclaration method1 = parseBodyDeclaration("void x(String a) { }").asMethodDeclaration();
        MethodDeclaration method2 = parseBodyDeclaration("int x(int z);").asMethodDeclaration();
        assertNotEquals(method1.getSignature(), method2.getSignature());
    }

    @Test
    public void signaturesDifferentVarargs() {
        MethodDeclaration method1 = parseBodyDeclaration("int x(int z);").asMethodDeclaration();
        MethodDeclaration method2 = parseBodyDeclaration("int x(int... z);").asMethodDeclaration();
        assertNotEquals(method1.getSignature(), method2.getSignature());
    }

    @Test
    public void signatureToString() {
        MethodDeclaration method1 = parseBodyDeclaration("int x(int z, String q);").asMethodDeclaration();
        assertEquals("x(int, String)", method1.getSignature().toString());
    }
}
