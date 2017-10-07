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

package com.github.javaparser.utils;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import org.junit.Test;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.visitor.ObjectIdentityEqualsVisitor;
import com.github.javaparser.ast.visitor.ObjectIdentityHashCodeVisitor;

public class VisitorListTest {

    @Test
    public void visitorAddAll() {
        List<CompilationUnit> list = new ArrayList<>();
        list.add(JavaParser.parse("class X{}"));
        list.add(JavaParser.parse("class X{}"));
        VisitorList<CompilationUnit> vList = new VisitorList<>(new ObjectIdentityHashCodeVisitor(),
                new ObjectIdentityEqualsVisitor());
        vList.addAll(list);
        for (int i = 0; i < list.size(); i++)
            assertEquals(list.get(i), vList.get(i));
    }

    @Test
    public void visitorAddAllAtIndex() {
        List<CompilationUnit> list = new ArrayList<>();
        list.add(JavaParser.parse("class X{}"));
        list.add(JavaParser.parse("class Y{}"));
        VisitorList<CompilationUnit> vList = new VisitorList<>(new ObjectIdentityHashCodeVisitor(),
                new ObjectIdentityEqualsVisitor());
        vList.add(JavaParser.parse("class A{}"));
        vList.add(JavaParser.parse("class B{}"));
        vList.addAll(2, list);
        vList.add(JavaParser.parse("class C{}"));
        for (int i = 0; i < list.size(); i++)
            assertEquals(list.get(i), vList.get(2 + i));
    }

    @Test
    public void visitorListContains() {
        CompilationUnit x1 = JavaParser.parse("class X{}");
        VisitorList<CompilationUnit> list = new VisitorList<>(new ObjectIdentityHashCodeVisitor(),
                new ObjectIdentityEqualsVisitor());
        list.add(x1);
        assertTrue(list.contains(x1));
    }

    @Test
    public void visitorListContainsAll() {
        List<CompilationUnit> list = new ArrayList<>();
        list.add(JavaParser.parse("class X{}"));
        list.add(JavaParser.parse("class X{}"));
        VisitorList<CompilationUnit> vList = new VisitorList<>(new ObjectIdentityHashCodeVisitor(),
                new ObjectIdentityEqualsVisitor());
        vList.addAll(list);
        assertTrue(vList.size() == 2 && vList.containsAll(list));
    }

    @Test
    public void visitorListIterator() {
        VisitorList<CompilationUnit> list = new VisitorList<>(new ObjectIdentityHashCodeVisitor(),
                new ObjectIdentityEqualsVisitor());
        CompilationUnit x1 = JavaParser.parse("class X{}");
        list.add(x1);
        CompilationUnit x2 = JavaParser.parse("class X{}");
        list.add(x2);
        Iterator<CompilationUnit> itr = list.iterator();
        assertEquals(x1, itr.next());
        itr.remove();
        assertTrue(list.size() == 1);
        assertEquals(x2, itr.next());
        itr.remove();
        assertTrue(list.size() == 0);
    }

    @Test
    public void visitorListListIterator() {
        VisitorList<CompilationUnit> list = new VisitorList<>(new ObjectIdentityHashCodeVisitor(),
                new ObjectIdentityEqualsVisitor());
        list.add(JavaParser.parse("class X{}"));
        list.add(JavaParser.parse("class X{}"));
        CompilationUnit x1 = JavaParser.parse("class X{}");
        list.add(x1);
        CompilationUnit x2 = JavaParser.parse("class X{}");
        list.add(x2);
        Iterator<CompilationUnit> itr = list.listIterator(2);
        assertEquals(x1, itr.next());
        itr.remove();
        assertTrue(list.size() == 3);
        assertEquals(x2, itr.next());
        itr.remove();
        assertTrue(list.size() == 2);
    }

    @Test
    public void visitorListRemove() {
        CompilationUnit x1 = JavaParser.parse("class X{}");
        VisitorList<CompilationUnit> list = new VisitorList<>(new ObjectIdentityHashCodeVisitor(),
                new ObjectIdentityEqualsVisitor());
        list.add(x1);
        assertTrue(list.remove(x1));
    }

    @Test
    public void visitorListRemoveAll() {
        List<CompilationUnit> list = new ArrayList<>();
        list.add(JavaParser.parse("class X{}"));
        list.add(JavaParser.parse("class X{}"));
        VisitorList<CompilationUnit> vList = new VisitorList<>(new ObjectIdentityHashCodeVisitor(),
                new ObjectIdentityEqualsVisitor());
        vList.addAll(list);
        vList.removeAll(list);
        assertTrue(vList.size() == 0);
    }

    @Test
    public void visitorListRetainAll() {
        List<CompilationUnit> list = new ArrayList<>();
        list.add(JavaParser.parse("class X{}"));
        list.add(JavaParser.parse("class X{}"));
        VisitorList<CompilationUnit> vList = new VisitorList<>(new ObjectIdentityHashCodeVisitor(),
                new ObjectIdentityEqualsVisitor());
        vList.addAll(list);
        vList.add(JavaParser.parse("class X{}"));
        vList.retainAll(list);
        assertTrue(vList.size() == 2);
    }

    @Test
    public void visitorListSubList() {
        VisitorList<CompilationUnit> list = new VisitorList<>(new ObjectIdentityHashCodeVisitor(),
                new ObjectIdentityEqualsVisitor());
        list.add(JavaParser.parse("class X{}"));
        list.add(JavaParser.parse("class X{}"));
        list.add(JavaParser.parse("class X{}"));
        list.add(JavaParser.parse("class X{}"));
        assertTrue(list.size() == 4);
        List<CompilationUnit> subLst = list.subList(1, 3);
        assertTrue(subLst.size() == 2);
        subLst.add(JavaParser.parse("class X{}"));
        assertTrue(subLst.size() == 3);
        assertTrue(list.size() == 5);

    }

    @Test
    public void visitorListToArray() {
        List<CompilationUnit> list = new ArrayList<>();
        list.add(JavaParser.parse("class X{}"));
        list.add(JavaParser.parse("class X{}"));
        List<CompilationUnit> vList = new VisitorList<>(new ObjectIdentityHashCodeVisitor(),
                new ObjectIdentityEqualsVisitor());
        vList.addAll(list);
        for (CompilationUnit u : vList.toArray(new CompilationUnit[2]))
            assertTrue(vList.contains(u));
    }

}
