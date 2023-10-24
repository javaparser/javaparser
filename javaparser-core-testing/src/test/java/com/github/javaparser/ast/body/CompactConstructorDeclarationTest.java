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
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class CompactConstructorDeclarationTest {
    @Test
    void testDefaultConstructor() {
        CompactConstructorDeclaration decl = new CompactConstructorDeclaration();
        assertNotNull(decl.getModifiers());
        assertNotNull(decl.getTypeParameters());
        assertNotNull(decl.getThrownExceptions());
        assertNotNull(decl.getName());
        assertNotNull(decl.getBody());
    }

    @Test
    void testConstructorWithName() {
        CompactConstructorDeclaration decl = new CompactConstructorDeclaration("MyConstructor");
        assertEquals("MyConstructor", decl.getNameAsString());
    }

    @Test
    void testConstructorWithModifiersAndName() {
        NodeList<Modifier> modifiers = new NodeList<>(Modifier.publicModifier());
        CompactConstructorDeclaration decl = new CompactConstructorDeclaration(modifiers, "MyConstructor");
        assertTrue(decl.getModifiers().contains(Modifier.publicModifier()));
        assertEquals("MyConstructor", decl.getNameAsString());
    }

    @Test
    void testSetBody() {
        CompactConstructorDeclaration decl = new CompactConstructorDeclaration();
        BlockStmt blockStmt = new BlockStmt();
        decl.setBody(blockStmt);
        assertSame(blockStmt, decl.getBody());
    }

    @Test
    void testSetModifiers() {
        CompactConstructorDeclaration decl = new CompactConstructorDeclaration();
        NodeList<Modifier> modifiers = new NodeList<>(Modifier.publicModifier());
        decl.setModifiers(modifiers);
        assertTrue(decl.getModifiers().contains(Modifier.publicModifier()));
    }

    @Test
    void testSetName() {
        CompactConstructorDeclaration decl = new CompactConstructorDeclaration();
        SimpleName name = new SimpleName("MyConstructor");
        decl.setName(name);
        assertSame(name, decl.getName());
    }

    @Test
    void testGetDeclarationAsString() {
        CompactConstructorDeclaration decl = new CompactConstructorDeclaration("MyConstructor");
        String declarationString = decl.getDeclarationAsString(true, true, true);
        assertEquals("public MyConstructor()", declarationString);
    }

    @Test
    public void testAppendThrowsIfRequested() {
        CompactConstructorDeclaration decl = new CompactConstructorDeclaration();
        decl.addThrownException(new ClassOrInterfaceType("IOException"));
        decl.addThrownException(new ClassOrInterfaceType("NullPointerException"));
        String result = decl.appendThrowsIfRequested(true);
        assertEquals(" throws IOException, NullPointerException", result);
    }

    @Test
    void testRemove() {
        CompactConstructorDeclaration decl = new CompactConstructorDeclaration();
        Modifier mod = new Modifier();
        decl.getModifiers().add(mod);

        boolean removed = decl.remove(mod);
        assertTrue(removed);

        removed = decl.remove(new BlockStmt());
        assertFalse(removed);
    }

    @Test
    void testClone() {
        CompactConstructorDeclaration decl = new CompactConstructorDeclaration();
        CompactConstructorDeclaration clone = decl.clone();
        assertNotSame(decl, clone);
    }


    @Test
    public void testReplace() {
        CompactConstructorDeclaration decl = new CompactConstructorDeclaration();

        SimpleName newName = new SimpleName("newName");
        assertTrue(decl.replace(decl.getName(), newName));
        assertEquals(newName, decl.getName());
    }



    @Test
    public void testIsCompactConstructorDeclaration() {
        CompactConstructorDeclaration decl = new CompactConstructorDeclaration();
        assertTrue(decl.isCompactConstructorDeclaration());
    }

    @Test
    public void testAsCompactConstructorDeclaration() {
        CompactConstructorDeclaration decl = new CompactConstructorDeclaration();
        assertEquals(decl, decl.asCompactConstructorDeclaration());
    }

    @Test
    public void testIfCompactConstructorDeclaration() {
        CompactConstructorDeclaration decl = new CompactConstructorDeclaration();
        decl.ifCompactConstructorDeclaration(d -> {
            assertTrue(d.isCompactConstructorDeclaration());
        });
    }

    @Test
    public void testToCompactConstructorDeclaration() {
        CompactConstructorDeclaration decl = new CompactConstructorDeclaration();
        assertTrue(decl.toCompactConstructorDeclaration().isPresent());
        assertEquals(decl,decl.toCompactConstructorDeclaration().get());
    }
}
