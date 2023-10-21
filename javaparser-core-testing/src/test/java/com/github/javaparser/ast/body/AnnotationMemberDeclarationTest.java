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

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class AnnotationMemberDeclarationTest {

    @Test
    void whenSettingNameTheParentOfNameIsAssigned() {
        AnnotationMemberDeclaration decl = new AnnotationMemberDeclaration();
        SimpleName name = new SimpleName("foo");
        decl.setName(name);
        assertTrue(name.getParentNode().isPresent());
        assertSame(decl, name.getParentNode().get());
    }

    @Test
    void removeDefaultValueWhenNoDefaultValueIsPresent() {
        AnnotationMemberDeclaration decl = new AnnotationMemberDeclaration();
        SimpleName name = new SimpleName("foo");
        decl.setName(name);

        decl.removeDefaultValue();

        assertFalse(decl.getDefaultValue().isPresent());
    }

    @Test
    void removeDefaultValueWhenDefaultValueIsPresent() {
        AnnotationMemberDeclaration decl = new AnnotationMemberDeclaration();
        SimpleName name = new SimpleName("foo");
        decl.setName(name);
        Expression defaultValue = new IntegerLiteralExpr("2");
        decl.setDefaultValue(defaultValue);

        decl.removeDefaultValue();

        assertFalse(defaultValue.getParentNode().isPresent());
    }

    @Test
    void testModifiersSetter() {
        AnnotationMemberDeclaration decl = new AnnotationMemberDeclaration();
        NodeList<Modifier> modifiers = new NodeList<>(Modifier.publicModifier(), Modifier.staticModifier());
        decl.setModifiers(modifiers);

        assertTrue(decl.getModifiers().contains(Modifier.publicModifier()));
        assertTrue(decl.getModifiers().contains(Modifier.staticModifier()));
    }

    @Test
    void testTypeSetter() {
        AnnotationMemberDeclaration decl = new AnnotationMemberDeclaration();
        ClassOrInterfaceType type = new ClassOrInterfaceType("String");
        decl.setType(type);

        assertEquals("String", decl.getType().asString());
    }

    @Test
    void testDefaultValueSetter() {
        AnnotationMemberDeclaration decl = new AnnotationMemberDeclaration();
        BooleanLiteralExpr defaultValue = new BooleanLiteralExpr(true);
        decl.setDefaultValue(defaultValue);

        assertTrue(decl.getDefaultValue().isPresent());
        assertTrue(((BooleanLiteralExpr) decl.getDefaultValue().get()).getValue());
    }

    @Test
    void testReplaceMethodForDefaultValue() {
        AnnotationMemberDeclaration decl = new AnnotationMemberDeclaration();
        LongLiteralExpr defaultValue = new LongLiteralExpr(123L);
        decl.setDefaultValue(defaultValue);

        LongLiteralExpr newDefaultValue = new LongLiteralExpr(456L);
        decl.replace(defaultValue, newDefaultValue);

        assertTrue(decl.getDefaultValue().isPresent());
        assertEquals(456L, ((LongLiteralExpr) decl.getDefaultValue().get()).asLong());
    }

    @Test
    void testReplaceMethodForOtherType() {
        AnnotationMemberDeclaration decl = new AnnotationMemberDeclaration();
        ClassOrInterfaceType type = new ClassOrInterfaceType("String");
        decl.setType(type);

        ClassOrInterfaceType newType = new ClassOrInterfaceType("Integer");
        assertTrue(decl.replace(type, newType));
        assertEquals("Integer", decl.getType().asString());
    }


    @Test
    void testRemoveMethod() {
        AnnotationMemberDeclaration decl = new AnnotationMemberDeclaration();

        Modifier publicMod = Modifier.publicModifier();
        NodeList<Modifier> modifiers = new NodeList<>(publicMod);
        decl.setModifiers(modifiers);

        assertTrue(decl.remove(publicMod));

        assertFalse(decl.remove(Modifier.protectedModifier()));
    }

    @Test
    void testCloneMethod() {
        AnnotationMemberDeclaration decl = new AnnotationMemberDeclaration();
        decl.setName(new SimpleName("foo"));
        decl.setType(new ClassOrInterfaceType("String"));
        AnnotationMemberDeclaration clonedDecl = decl.clone();

        assertEquals(decl.getName().asString(), clonedDecl.getName().asString());
        assertEquals(decl.getType().asString(), clonedDecl.getType().asString());
    }

    @Test
    void testIsAnnotationMemberDeclaration() {
        AnnotationMemberDeclaration decl = new AnnotationMemberDeclaration();
        assertTrue(decl.isAnnotationMemberDeclaration());
    }

    @Test
    void testAsAnnotationMemberDeclaration() {
        AnnotationMemberDeclaration decl = new AnnotationMemberDeclaration();
        assertEquals(decl, decl.asAnnotationMemberDeclaration());
    }

    @Test
    void testIfAnnotationMemberDeclaration() {
        AnnotationMemberDeclaration decl = new AnnotationMemberDeclaration();
        decl.ifAnnotationMemberDeclaration(annotationDecl -> assertEquals(decl, annotationDecl));
    }

    @Test
    void testToAnnotationMemberDeclaration() {
        AnnotationMemberDeclaration decl = new AnnotationMemberDeclaration();
        assertTrue(decl.toAnnotationMemberDeclaration().isPresent());
        assertEquals(decl, decl.toAnnotationMemberDeclaration().get());
    }




}
