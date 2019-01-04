/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2017 The JavaParser Team.
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

package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.observer.AstObserverAdapter;
import com.github.javaparser.ast.observer.ObservableProperty;
import org.junit.jupiter.api.Test;

import java.util.LinkedList;
import java.util.List;

import static com.github.javaparser.ast.Modifier.Keyword.PRIVATE;
import static com.github.javaparser.ast.Modifier.Keyword.PUBLIC;
import static com.github.javaparser.ast.Modifier.Keyword.STATIC;
import static com.github.javaparser.ast.Modifier.Keyword.SYNCHRONIZED;
import static com.github.javaparser.ast.Modifier.createModifierList;
import static org.junit.jupiter.api.Assertions.assertEquals;

class NodeWithModifiersTest {

    @Test
    void addModifierWorks() {
        ClassOrInterfaceDeclaration decl = new ClassOrInterfaceDeclaration(new NodeList<>(),
                false, "Foo");
        decl.addModifier(PUBLIC);
        assertEquals(createModifierList(PUBLIC), decl.getModifiers());
    }

    @Test
    void addModifierTriggerNotification() {
        List<String> changes = new LinkedList<>();
        ClassOrInterfaceDeclaration decl = new ClassOrInterfaceDeclaration(new NodeList<>(),
                false, "Foo");
        decl.register(new AstObserverAdapter() {
            @Override
            public void propertyChange(Node observedNode, ObservableProperty property, Object oldValue, Object newValue) {
                changes.add("property " + property.name() + " is changed to " + newValue);
            }
        });
        decl.addModifier(PUBLIC);
        assertEquals(1, changes.size());
        assertEquals("property MODIFIERS is changed to [public ]", changes.get(0));
    }

    @Test
    void removeExistingModifier() {
        NodeWithModifiers node = anythingWithModifiers(PUBLIC);
        node.removeModifier(PUBLIC);
        assertEquals(0, node.getModifiers().size());
    }

    @Test
    void ignoreNotExistingModifiersOnRemove() {
        NodeWithModifiers node = anythingWithModifiers(PUBLIC);
        node.removeModifier(PRIVATE);

        assertEquals(createModifierList(PUBLIC), node.getModifiers());
    }

    @Test
    void keepModifiersThatShouldNotBeRemoved() {
        NodeWithModifiers node = anythingWithModifiers(PUBLIC, STATIC, SYNCHRONIZED);
        node.removeModifier(PUBLIC, PRIVATE, STATIC);

        assertEquals(createModifierList(SYNCHRONIZED), node.getModifiers());
    }

    private NodeWithModifiers anythingWithModifiers(Modifier.Keyword ... keywords) {
        ClassOrInterfaceDeclaration foo = new ClassOrInterfaceDeclaration(new NodeList<>(), false, "Foo");
        foo.addModifier(keywords);
        return foo;
    }
}