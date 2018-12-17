/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2016 The JavaParser Team.
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

package com.github.javaparser.ast;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.observer.AstObserver;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.type.PrimitiveType;
import org.junit.Test;

import java.util.Arrays;
import java.util.EnumSet;
import java.util.LinkedList;
import java.util.List;

import static com.github.javaparser.ast.NodeList.nodeList;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class NodeListTest {

    private AstObserver createObserver(List<String> changes) {
        return new AstObserver() {
            @Override
            public void propertyChange(Node observedNode, ObservableProperty property, Object oldValue, Object newValue) {
                changes.add(String.format("change of property %s for %s: from '%s' to '%s'", property, observedNode, oldValue, newValue));
            }

            @Override
            public void parentChange(Node observedNode, Node previousParent, Node newParent) {
                changes.add(String.format("setting parent for %s: was %s, now is %s", observedNode, previousParent, newParent));
            }

            @Override
            public void listChange(NodeList observedNode, ListChangeType type, int index, Node nodeAddedOrRemoved) {
                changes.add(String.format("'%s' %s in list at %d", nodeAddedOrRemoved, type, index));
            }

            @Override
            public void listReplacement(NodeList observedNode, int index, Node oldNode, Node newNode) {
                changes.add(String.format("'%s' %s in list at %d", oldNode, ListChangeType.REMOVAL, index));
                changes.add(String.format("'%s' %s in list at %d", newNode, ListChangeType.ADDITION, index));
            }
        };
    }

    private FieldDeclaration createIntField(String name) {
        return new FieldDeclaration(EnumSet.noneOf(Modifier.class), PrimitiveType.intType(), name);
    }

    @Test
    public void addAllWithoutIndex() {
        List<String> changes = new LinkedList<>();
        String code = "class A { void foo(int p) { }}";
        CompilationUnit cu = JavaParser.parse(code);
        ClassOrInterfaceDeclaration cd = cu.getClassByName("A").get();
        cd.getMembers().register(createObserver(changes));

        cd.getMembers().addAll(Arrays.asList(createIntField("a"), createIntField("b"), createIntField("c")));
        assertEquals(Arrays.asList("'int a;' ADDITION in list at 1",
                "'int b;' ADDITION in list at 2",
                "'int c;' ADDITION in list at 3"), changes);
    }

    @Test
    public void addAllWithIndex() {
        List<String> changes = new LinkedList<>();
        String code = "class A { void foo(int p) { }}";
        CompilationUnit cu = JavaParser.parse(code);
        ClassOrInterfaceDeclaration cd = cu.getClassByName("A").get();
        cd.getMembers().register(createObserver(changes));

        cd.getMembers().addAll(0, Arrays.asList(createIntField("a"), createIntField("b"), createIntField("c")));
        assertEquals(Arrays.asList("'int a;' ADDITION in list at 0",
                "'int b;' ADDITION in list at 1",
                "'int c;' ADDITION in list at 2"), changes);
    }

    @Test
    public void clear() {
        List<String> changes = new LinkedList<>();
        String code = "class A { int a; int b; int c; }";
        CompilationUnit cu = JavaParser.parse(code);
        ClassOrInterfaceDeclaration cd = cu.getClassByName("A").get();
        cd.getMembers().register(createObserver(changes));

        cd.getMembers().clear();
        assertEquals(Arrays.asList("'int a;' REMOVAL in list at 0",
                "'int b;' REMOVAL in list at 0",
                "'int c;' REMOVAL in list at 0"), changes);
    }

    @Test
    public void set() {
        List<String> changes = new LinkedList<>();
        String code = "class A { int a; int b; int c; }";
        CompilationUnit cu = JavaParser.parse(code);
        ClassOrInterfaceDeclaration cd = cu.getClassByName("A").get();
        cd.getMembers().register(createObserver(changes));

        cd.getMembers().set(1, createIntField("d"));
        assertEquals(Arrays.asList("'int b;' REMOVAL in list at 1",
                "'int d;' ADDITION in list at 1"), changes);
    }

    @Test
    public void removeNode() {
        List<String> changes = new LinkedList<>();
        String code = "class A { int a; int b; int c; int d; int e; }";
        CompilationUnit cu = JavaParser.parse(code);
        ClassOrInterfaceDeclaration cd = cu.getClassByName("A").get();
        cd.getMembers().register(createObserver(changes));

        cd.getMembers().remove(cd.getFieldByName("c").get());
        assertEquals(Arrays.asList("'int c;' REMOVAL in list at 2"), changes);
    }

    @Test
    public void removeFirstNode() {
        List<String> changes = new LinkedList<>();
        String code = "class A { int a; int b; int c; int d; int e; }";
        CompilationUnit cu = JavaParser.parse(code);
        ClassOrInterfaceDeclaration cd = cu.getClassByName("A").get();
        cd.getMembers().register(createObserver(changes));

        cd.getMembers().removeFirst();
        assertEquals(Arrays.asList("'int a;' REMOVAL in list at 0"), changes);
        assertEquals(cd.getMembers().size(), 4);

        for (int i = 3; i >= 0; i--) {
            assertTrue(cd.getMembers().removeFirst() != null);
            assertEquals(cd.getMembers().size(), i);
        }

        assertEquals(cd.getMembers().size(), 0);
    }

    @Test
    public void removeLastNode() {
        List<String> changes = new LinkedList<>();
        String code = "class A { int a; int b; int c; int d; int e; }";
        CompilationUnit cu = JavaParser.parse(code);
        ClassOrInterfaceDeclaration cd = cu.getClassByName("A").get();
        cd.getMembers().register(createObserver(changes));

        cd.getMembers().removeLast();
        assertEquals(Arrays.asList("'int e;' REMOVAL in list at 4"), changes);
        assertEquals(cd.getMembers().size(), 4);

        for (int i = 3; i >= 0; i--) {
            assertTrue(cd.getMembers().removeLast() != null);
            assertEquals(cd.getMembers().size(), i);
        }

        assertEquals(cd.getMembers().size(), 0);
    }

    @Test
    public void removeObject() {
        List<String> changes = new LinkedList<>();
        String code = "class A { int a; int b; int c; int d; int e; }";
        CompilationUnit cu = JavaParser.parse(code);
        ClassOrInterfaceDeclaration cd = cu.getClassByName("A").get();
        cd.getMembers().register(createObserver(changes));

        cd.getMembers().remove("hi");
        assertEquals(Arrays.asList(), changes);
    }

    @Test
    public void removeAll() {
        List<String> changes = new LinkedList<>();
        String code = "class A { int a; int b; int c; int d; int e; }";
        CompilationUnit cu = JavaParser.parse(code);
        ClassOrInterfaceDeclaration cd = cu.getClassByName("A").get();
        cd.getMembers().register(createObserver(changes));

        cd.getMembers().removeAll(Arrays.asList(cd.getFieldByName("b").get(), "foo", cd.getFieldByName("d").get()));
        assertEquals(Arrays.asList("'int b;' REMOVAL in list at 1",
                "'int d;' REMOVAL in list at 2"), changes);
    }

    @Test
    public void retainAll() {
        List<String> changes = new LinkedList<>();
        String code = "class A { int a; int b; int c; int d; int e; }";
        CompilationUnit cu = JavaParser.parse(code);
        ClassOrInterfaceDeclaration cd = cu.getClassByName("A").get();
        cd.getMembers().register(createObserver(changes));

        cd.getMembers().retainAll(Arrays.asList(cd.getFieldByName("b").get(), "foo", cd.getFieldByName("d").get()));
        assertEquals(Arrays.asList("'int a;' REMOVAL in list at 0",
                "'int c;' REMOVAL in list at 1",
                "'int e;' REMOVAL in list at 2"), changes);
    }

    @Test
    public void replaceAll() {
        List<String> changes = new LinkedList<>();
        String code = "class A { int a; int b; int c; }";
        CompilationUnit cu = JavaParser.parse(code);
        ClassOrInterfaceDeclaration cd = cu.getClassByName("A").get();
        cd.getMembers().register(createObserver(changes));

        cd.getMembers().replaceAll(bodyDeclaration -> {
            FieldDeclaration clone = (FieldDeclaration) bodyDeclaration.clone();
            SimpleName id = clone.getVariable(0).getName();
            id.setIdentifier(id.getIdentifier().toUpperCase());
            return clone;
        });
        assertEquals(Arrays.asList("'int a;' REMOVAL in list at 0", "'int A;' ADDITION in list at 0",
                "'int b;' REMOVAL in list at 1", "'int B;' ADDITION in list at 1",
                "'int c;' REMOVAL in list at 2", "'int C;' ADDITION in list at 2"), changes);
    }

    @Test
    public void removeIf() {
        List<String> changes = new LinkedList<>();
        String code = "class A { int a; int longName; int c; }";
        CompilationUnit cu = JavaParser.parse(code);
        ClassOrInterfaceDeclaration cd = cu.getClassByName("A").get();
        cd.getMembers().register(createObserver(changes));

        cd.getMembers().removeIf(m -> ((FieldDeclaration) m).getVariable(0).getName().getIdentifier().length() > 3);
        assertEquals(Arrays.asList("'int longName;' REMOVAL in list at 1"), changes);
    }

    @Test
    public void replace() {
        final NodeList<Name> list = nodeList(new Name("a"), new Name("b"), new Name("c"));

        final boolean replaced = list.replace(new Name("b"), new Name("z"));

        assertEquals(true, replaced);
        assertEquals(3, list.size());
        assertEquals("a", list.get(0).asString());
        assertEquals("z", list.get(1).asString());
        assertEquals("c", list.get(2).asString());
    }

    @Test
    public void toStringTest() {
        final NodeList<Name> list = nodeList(new Name("abc"), new Name("bcd"), new Name("cde"));

        assertEquals("[abc, bcd, cde]", list.toString());
    }

    @Test
    public void addFirst() {
        final NodeList<Name> list = nodeList(new Name("abc"), new Name("bcd"), new Name("cde"));

        list.addFirst(new Name("xxx"));

        assertEquals("[xxx, abc, bcd, cde]", list.toString());
    }

    @Test
    public void addLast() {
        final NodeList<Name> list = nodeList(new Name("abc"), new Name("bcd"), new Name("cde"));

        list.addLast(new Name("xxx"));

        assertEquals("[abc, bcd, cde, xxx]", list.toString());
    }

    @Test
    public void addBefore() {
        Name n = new Name("bcd");
        final NodeList<Name> list = nodeList(new Name("abc"), n, new Name("cde"));

        list.addBefore(new Name("xxx"), n);

        assertEquals("[abc, xxx, bcd, cde]", list.toString());
    }

    @Test
    public void addAfter() {
        Name n = new Name("bcd");
        final NodeList<Name> list = nodeList(new Name("abc"), n, new Name("cde"));

        list.addAfter(new Name("xxx"), n);

        assertEquals("[abc, bcd, xxx, cde]", list.toString());
    }

    @Test
    public void addBeforeFirst() {
        Name abc = new Name("abc");
        final NodeList<Name> list = nodeList(abc, new Name("bcd"), new Name("cde"));

        list.addBefore(new Name("xxx"), abc);

        assertEquals("[xxx, abc, bcd, cde]", list.toString());
    }

    @Test
    public void addAfterLast() {
        Name cde = new Name("cde");
        final NodeList<Name> list = nodeList(new Name("abc"), new Name("bcd"), cde);

        list.addAfter(new Name("xxx"), cde);

        assertEquals("[abc, bcd, cde, xxx]", list.toString());
    }
}
