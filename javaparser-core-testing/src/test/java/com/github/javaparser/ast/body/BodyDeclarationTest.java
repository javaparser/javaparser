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

import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import org.junit.jupiter.api.Test;

import java.util.Optional;

import static org.junit.jupiter.api.Assertions.*;

class BodyDeclarationTest {

    // A concrete subclass of BodyDeclaration for testing
    private static class ConcreteBodyDeclaration extends BodyDeclaration<ConcreteBodyDeclaration> {
        @Override
        public ConcreteBodyDeclaration clone() {
            return (ConcreteBodyDeclaration) super.clone();
        }

        @Override
        public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
            return null;
        }

        @Override
        public <A> void accept(VoidVisitor<A> v, A arg) {

        }
    }

    // Mock AnnotationExpr class for testing purposes
    private static class MockAnnotationExpr extends AnnotationExpr {
        @Override
        public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
            return null;
        }

        @Override
        public <A> void accept(VoidVisitor<A> v, A arg) {

        }
    }

    @Test
    void testSetAnnotations() {
        ConcreteBodyDeclaration decl = new ConcreteBodyDeclaration();

        assertTrue(decl.getAnnotations().isEmpty());

        NodeList<AnnotationExpr> annotations = new NodeList<>(new MarkerAnnotationExpr("Override"));
        decl.setAnnotations(annotations);

        assertEquals(1, decl.getAnnotations().size());
        assertEquals("Override", decl.getAnnotations().get(0).getNameAsString());
    }

    @Test
    void testRemoveAnnotation() {
        ConcreteBodyDeclaration decl = new ConcreteBodyDeclaration();
        NodeList<AnnotationExpr> annotations = new NodeList<>(new MarkerAnnotationExpr("Override"));
        decl.setAnnotations(annotations);

        assertTrue(decl.remove(decl.getAnnotations().get(0)));
        assertTrue(decl.getAnnotations().isEmpty());
    }

    @Test
    public void testReplace() {
        ConcreteBodyDeclaration declaration = new ConcreteBodyDeclaration();
        AnnotationExpr mockAnnotation = new MockAnnotationExpr();
        declaration.getAnnotations().add(mockAnnotation);
        AnnotationExpr newAnnotation = new MockAnnotationExpr();
        assertTrue(declaration.replace(mockAnnotation, newAnnotation));
    }

    @Test
    public void testIsAnnotationDeclaration() {
        ConcreteBodyDeclaration decl = new ConcreteBodyDeclaration();
        assertFalse(decl.isAnnotationDeclaration());
    }

    @Test
    public void testIfAnnotationDeclaration() {
        ConcreteBodyDeclaration decl = new ConcreteBodyDeclaration();
        decl.ifAnnotationDeclaration(annotationDeclaration -> fail("Action should not be executed"));
    }

    @Test
    public void testTypeCastingMethods() {
        ConcreteBodyDeclaration decl = new ConcreteBodyDeclaration();

        assertFalse(decl.isAnnotationDeclaration());
        assertThrows(IllegalStateException.class, decl::asAnnotationDeclaration);

        assertFalse(decl.isAnnotationMemberDeclaration());
        assertThrows(IllegalStateException.class, decl::asAnnotationMemberDeclaration);

        assertFalse(decl.isCallableDeclaration());
        assertThrows(IllegalStateException.class, decl::asCallableDeclaration);

        assertFalse(decl.isClassOrInterfaceDeclaration());
        assertThrows(IllegalStateException.class, decl::asClassOrInterfaceDeclaration);

        assertFalse(decl.isConstructorDeclaration());
        assertThrows(IllegalStateException.class, decl::asConstructorDeclaration);

        assertFalse(decl.isCompactConstructorDeclaration());
        assertThrows(IllegalStateException.class, decl::asCompactConstructorDeclaration);

        assertFalse(decl.isEnumConstantDeclaration());
        assertThrows(IllegalStateException.class, decl::asEnumConstantDeclaration);

        assertFalse(decl.isEnumDeclaration());
        assertThrows(IllegalStateException.class, decl::asEnumDeclaration);

        assertFalse(decl.isFieldDeclaration());
        assertThrows(IllegalStateException.class, decl::asFieldDeclaration);

        assertFalse(decl.isInitializerDeclaration());
        assertThrows(IllegalStateException.class, decl::asInitializerDeclaration);

        assertFalse(decl.isMethodDeclaration());
        assertThrows(IllegalStateException.class, decl::asMethodDeclaration);

        assertFalse(decl.isTypeDeclaration());
        assertThrows(IllegalStateException.class, decl::asTypeDeclaration);

        assertFalse(decl.isRecordDeclaration());
        assertThrows(IllegalStateException.class, decl::asRecordDeclaration);

        assertEquals(Optional.empty(), decl.toAnnotationDeclaration());
        assertEquals(Optional.empty(), decl.toAnnotationMemberDeclaration());
        assertEquals(Optional.empty(), decl.toCallableDeclaration());
        assertEquals(Optional.empty(), decl.toClassOrInterfaceDeclaration());
        assertEquals(Optional.empty(), decl.toConstructorDeclaration());
        assertEquals(Optional.empty(), decl.toEnumConstantDeclaration());
        assertEquals(Optional.empty(), decl.toEnumDeclaration());
        assertEquals(Optional.empty(), decl.toFieldDeclaration());
        assertEquals(Optional.empty(), decl.toInitializerDeclaration());
        assertEquals(Optional.empty(), decl.toMethodDeclaration());
        assertEquals(Optional.empty(), decl.toTypeDeclaration());
        assertEquals(Optional.empty(), decl.toRecordDeclaration());
        assertEquals(Optional.empty(), decl.toCompactConstructorDeclaration());
    }
    
}
