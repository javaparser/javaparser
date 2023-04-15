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

import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.parseBodyDeclaration;
import static org.junit.jupiter.api.Assertions.*;

class MethodDeclarationTest {
    @Test
    void annotationsAllowedAfterGenericsAndBeforeReturnType() {
        parseBodyDeclaration("public <T> @Abc String method() {return null;}");
    }

    @Test
    void annotationsAllowedBeforeGenerics() {
        parseBodyDeclaration("public @Abc <T> String method() {return null;}");
    }

    @Test
    void explicitReceiverParameters1() {
        MethodDeclaration method = parseBodyDeclaration("void InnerInner(@mypackage.Anno Source.@mypackage.Anno Inner Source.Inner.this) { }").asMethodDeclaration();
        assertEquals("Source.Inner.this", method.getReceiverParameter().get().getNameAsString());
    }

    @Test
    void explicitReceiverParameters2() {
        MethodDeclaration method = parseBodyDeclaration("void x(A this) { }").asMethodDeclaration();
        assertEquals("this", method.getReceiverParameter().get().getNameAsString());
    }

    @Test
    void explicitReceiverParameters3() {
        MethodDeclaration method = parseBodyDeclaration("void x(A that) { }").asMethodDeclaration();
        assertFalse(method.getReceiverParameter().isPresent());
    }

    @Test
    void signaturesEqual() {
        MethodDeclaration method1 = parseBodyDeclaration("void x(String a) { }").asMethodDeclaration();
        MethodDeclaration method2 = parseBodyDeclaration("int x(String z);").asMethodDeclaration();
        assertEquals(method1.getSignature(), method2.getSignature());
    }

    @Test
    void signaturesEqualWhenGenericsDiffer() {
        MethodDeclaration method1 = parseBodyDeclaration("void x(List<Long> a) { }").asMethodDeclaration();
        MethodDeclaration method2 = parseBodyDeclaration("void x(List<Integer> a) { }").asMethodDeclaration();
        assertEquals(method1.getSignature(), method2.getSignature());
    }

    @Test
    void signaturesEqualWhenAnnotationsDiffer() {
        MethodDeclaration method1 = parseBodyDeclaration("void x(@A @B List a) { }").asMethodDeclaration();
        MethodDeclaration method2 = parseBodyDeclaration("void x(@C List a) { }").asMethodDeclaration();
        assertEquals(method1.getSignature(), method2.getSignature());
    }

    @Test
    void signaturesDifferentName() {
        MethodDeclaration method1 = parseBodyDeclaration("void x(String a) { }").asMethodDeclaration();
        MethodDeclaration method2 = parseBodyDeclaration("int y(String z);").asMethodDeclaration();
        assertNotEquals(method1.getSignature(), method2.getSignature());
    }

    @Test
    void signaturesDifferentTypes() {
        MethodDeclaration method1 = parseBodyDeclaration("void x(String a) { }").asMethodDeclaration();
        MethodDeclaration method2 = parseBodyDeclaration("int x(int z);").asMethodDeclaration();
        assertNotEquals(method1.getSignature(), method2.getSignature());
    }

    @Test
    void signaturesDifferentVarargs() {
        MethodDeclaration method1 = parseBodyDeclaration("int x(int z);").asMethodDeclaration();
        MethodDeclaration method2 = parseBodyDeclaration("int x(int... z);").asMethodDeclaration();
        assertNotEquals(method1.getSignature(), method2.getSignature());
    }

    @Test
    void signatureToString() {
        MethodDeclaration method1 = parseBodyDeclaration("int x(int z, String q);").asMethodDeclaration();
        assertEquals("x(int, String)", method1.getSignature().toString());
    }
    
    @Test
    void isVariableArityMethod() {
        MethodDeclaration method1 = parseBodyDeclaration("int x(int... z);").asMethodDeclaration();
        assertTrue(method1.isVariableArityMethod());
        MethodDeclaration method2 = parseBodyDeclaration("int x(int i, int... z);").asMethodDeclaration();
        assertTrue(method2.isVariableArityMethod());
    }
    
    @Test
    void isFixedArityMethod() {
        MethodDeclaration method1 = parseBodyDeclaration("int x(int z);").asMethodDeclaration();
        assertTrue(method1.isFixedArityMethod());
        MethodDeclaration method2 = parseBodyDeclaration("int x();").asMethodDeclaration();
        assertTrue(method2.isFixedArityMethod());
    }
}
