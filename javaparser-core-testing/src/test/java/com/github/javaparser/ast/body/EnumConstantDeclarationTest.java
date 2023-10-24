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

import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class EnumConstantDeclarationTest {

    @Test
    public void testDefaultConstructor() {
        EnumConstantDeclaration enumConstant = new EnumConstantDeclaration();
        assertNotNull(enumConstant.getName());
        assertTrue(enumConstant.getArguments().isEmpty());
        assertTrue(enumConstant.getClassBody().isEmpty());
    }

    @Test
    public void testStringConstructor() {
        EnumConstantDeclaration enumConstant = new EnumConstantDeclaration("TEST");
        assertEquals("TEST", enumConstant.getName().asString());
        assertTrue(enumConstant.getArguments().isEmpty());
        assertTrue(enumConstant.getClassBody().isEmpty());
    }

    @Test
    public void testSetArguments() {
        EnumConstantDeclaration enumConstant = new EnumConstantDeclaration();
        enumConstant.setArguments(new com.github.javaparser.ast.NodeList<>(new NameExpr("arg1")));
        assertEquals(1, enumConstant.getArguments().size());
        assertEquals("arg1", enumConstant.getArguments().get(0).toString());
    }

    @Test
    public void testSetName() {
        EnumConstantDeclaration enumConstant = new EnumConstantDeclaration();
        enumConstant.setName(new SimpleName("NEW_ENUM_CONSTANT"));
        assertEquals("NEW_ENUM_CONSTANT", enumConstant.getName().asString());
    }

    @Test
    public void testClone() {
        EnumConstantDeclaration enumConstant = new EnumConstantDeclaration("MY_ENUM_CONSTANT");
        EnumConstantDeclaration clone = enumConstant.clone();
        assertNotSame(enumConstant, clone);
        assertEquals(enumConstant.getName(), clone.getName());
    }

    @Test
    public void testRemove() {
        EnumConstantDeclaration enumConstant = new EnumConstantDeclaration();
        NameExpr arg1 = new NameExpr("arg1");
        enumConstant.getArguments().add(arg1);

        MethodDeclaration methodDeclaration = new MethodDeclaration();
        enumConstant.getClassBody().add(methodDeclaration);

        assertTrue(enumConstant.remove(arg1));
        assertFalse(enumConstant.getArguments().contains(arg1));

        assertTrue(enumConstant.remove(methodDeclaration));
        assertFalse(enumConstant.getClassBody().contains(methodDeclaration));
    }

    @Test
    public void testReplace() {
        EnumConstantDeclaration enumConstant = new EnumConstantDeclaration();
        SimpleName oldName = new SimpleName("OldName");
        SimpleName newName = new SimpleName("NewName");
        enumConstant.setName(oldName);

        NameExpr arg1 = new NameExpr("arg1");
        NameExpr arg2 = new NameExpr("arg2");
        enumConstant.getArguments().add(arg1);

        assertTrue(enumConstant.replace(oldName, newName));
        assertEquals(newName, enumConstant.getName());

        assertTrue(enumConstant.replace(arg1, arg2));
        assertFalse(enumConstant.getArguments().contains(arg1));
        assertTrue(enumConstant.getArguments().contains(arg2));
    }

    @Test
    public void testTypeCastingMethods() {
        EnumConstantDeclaration enumConstant = new EnumConstantDeclaration();

        assertTrue(enumConstant.isEnumConstantDeclaration());
        assertEquals(enumConstant, enumConstant.asEnumConstantDeclaration());

        enumConstant.ifEnumConstantDeclaration(e -> {
            assertTrue(e instanceof EnumConstantDeclaration);
        });

        assertTrue(enumConstant.toEnumConstantDeclaration().isPresent());
    }


}
