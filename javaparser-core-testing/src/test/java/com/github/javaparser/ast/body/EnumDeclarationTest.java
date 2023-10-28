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

import com.github.javaparser.ast.type.ClassOrInterfaceType;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class EnumDeclarationTest {

    @Test
    public void testDefaultConstructor() {
        EnumDeclaration enumDeclaration = new EnumDeclaration();
        assertNotNull(enumDeclaration);
        assertTrue(enumDeclaration.getEntries().isEmpty());
        assertTrue(enumDeclaration.getImplementedTypes().isEmpty());
    }

    @Test
    public void testEntriesManipulation() {
        EnumDeclaration enumDeclaration = new EnumDeclaration();
        EnumConstantDeclaration entry = new EnumConstantDeclaration("TEST");
        enumDeclaration.addEntry(entry);

        assertEquals(1, enumDeclaration.getEntries().size());
        assertEquals("TEST", enumDeclaration.getEntry(0).getNameAsString());

        EnumConstantDeclaration newEntry = new EnumConstantDeclaration("NewTEST");
        enumDeclaration.setEntry(0, newEntry);
        assertEquals("NewTEST", enumDeclaration.getEntry(0).getNameAsString());

        enumDeclaration.remove(newEntry);
        assertTrue(enumDeclaration.getEntries().isEmpty());
    }

    @Test
    void testAddEnumConstant() {
        EnumDeclaration enumDeclaration = new EnumDeclaration();
        enumDeclaration.addEnumConstant("TEST_CONSTANT");

        assertTrue(enumDeclaration.getEntries().isNonEmpty());
        assertEquals("TEST_CONSTANT", enumDeclaration.getEntry(0).getName().asString());
    }

    @Test
    public void testRemove() {
        EnumDeclaration enumDeclaration = new EnumDeclaration();
        ClassOrInterfaceType implementedType = new ClassOrInterfaceType("Serializable");
        enumDeclaration.getImplementedTypes().add(implementedType);

        assertEquals(1, enumDeclaration.getImplementedTypes().size());
        assertEquals("Serializable", enumDeclaration.getImplementedTypes().get(0).asString());

        enumDeclaration.remove(implementedType);
        assertTrue(enumDeclaration.getImplementedTypes().isEmpty());
    }

    @Test
    void testClone() {
        EnumDeclaration enumDeclaration = new EnumDeclaration();
        EnumDeclaration clonedEnumDeclaration = enumDeclaration.clone();

        assertNotNull(clonedEnumDeclaration);
        assertNotSame(enumDeclaration, clonedEnumDeclaration);
    }

    @Test
    void testGetMetaModel() {
        EnumDeclaration enumDeclaration = new EnumDeclaration();

        assertNotNull(enumDeclaration.getMetaModel());
    }

    @Test
    public void testReplace() {
        EnumDeclaration enumDeclaration = new EnumDeclaration();
        EnumConstantDeclaration entry1 = new EnumConstantDeclaration("TEST1");
        EnumConstantDeclaration entry2 = new EnumConstantDeclaration("TEST2");
        enumDeclaration.addEntry(entry1);

        assertTrue(enumDeclaration.replace(entry1, entry2));
        assertEquals("TEST2", enumDeclaration.getEntry(0).getNameAsString());

        ClassOrInterfaceType type1 = new ClassOrInterfaceType("Serializable");
        ClassOrInterfaceType type2 = new ClassOrInterfaceType("Cloneable");
        enumDeclaration.getImplementedTypes().add(type1);

        assertTrue(enumDeclaration.replace(type1, type2));
        assertEquals("Cloneable", enumDeclaration.getImplementedTypes().get(0).asString());
    }

    @Test
    public void testTypeCastingMethods() {
        EnumDeclaration enumDeclaration = new EnumDeclaration();

        assertTrue(enumDeclaration.isEnumDeclaration());
        assertEquals(enumDeclaration, enumDeclaration.asEnumDeclaration());

        enumDeclaration.ifEnumDeclaration(e -> {
            assertTrue(e instanceof EnumDeclaration);
        });

        assertTrue(enumDeclaration.toEnumDeclaration().isPresent());
    }
}
