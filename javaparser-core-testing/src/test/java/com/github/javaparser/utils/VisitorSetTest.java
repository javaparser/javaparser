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

import static com.github.javaparser.StaticJavaParser.parse;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import org.junit.jupiter.api.Test;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.visitor.ObjectIdentityEqualsVisitor;
import com.github.javaparser.ast.visitor.ObjectIdentityHashCodeVisitor;

class VisitorSetTest {

    @Test
    void normalEqualsDoesDeepCompare() {
        Set<CompilationUnit> set = new HashSet<>();
        set.add(parse("class X{}"));
        set.add(parse("class X{}"));
        assertEquals(1, set.size());
    }

    @Test
    void objectIdentityEqualsDoesShallowCompare() {
        Set<CompilationUnit> set = new VisitorSet<>(new ObjectIdentityHashCodeVisitor(),
                new ObjectIdentityEqualsVisitor());
        set.add(parse("class X{}"));
        set.add(parse("class X{}"));
        assertEquals(2, set.size());
    }

    @Test
    void visitorSetContains() {
        CompilationUnit x1 = parse("class X{}");
        Set<CompilationUnit> set = new VisitorSet<>(new ObjectIdentityHashCodeVisitor(),
                new ObjectIdentityEqualsVisitor());
        set.add(x1);
        assertTrue(set.contains(x1));
    }

    @Test
    void visitorSetContainsAll() {
        List<CompilationUnit> list = new ArrayList<>();
        list.add(parse("class X{}"));
        list.add(parse("class X{}"));
        Set<CompilationUnit> set = new VisitorSet<>(new ObjectIdentityHashCodeVisitor(),
                new ObjectIdentityEqualsVisitor());
        set.addAll(list);
        assertTrue(set.size() == 2 && set.containsAll(list));
    }

    @Test
    void visitorSetIterator() {
        Set<CompilationUnit> set = new VisitorSet<>(new ObjectIdentityHashCodeVisitor(),
                new ObjectIdentityEqualsVisitor());
        CompilationUnit x1 = parse("class X{}");
        set.add(x1);
        CompilationUnit x2 = parse("class X{}");
        set.add(x2);
        Iterator<CompilationUnit> itr = set.iterator();
        assertEquals(x1, itr.next());
        itr.remove();
        assertEquals(1, set.size());
        assertEquals(x2, itr.next());
        itr.remove();
        assertEquals(0, set.size());
    }

    @Test
    void visitorSetRemove() {
        CompilationUnit x1 = parse("class X{}");
        Set<CompilationUnit> set = new VisitorSet<>(new ObjectIdentityHashCodeVisitor(),
                new ObjectIdentityEqualsVisitor());
        set.add(x1);
        assertTrue(set.remove(x1));
    }

    @Test
    void visitorSetRemoveAll() {
        List<CompilationUnit> list = new ArrayList<>();
        list.add(parse("class X{}"));
        list.add(parse("class X{}"));
        Set<CompilationUnit> set = new VisitorSet<>(new ObjectIdentityHashCodeVisitor(),
                new ObjectIdentityEqualsVisitor());
        set.addAll(list);
        set.removeAll(list);
        assertEquals(0, set.size());
    }

    @Test
    void visitorSetRetainAll() {
        List<CompilationUnit> list = new ArrayList<>();
        list.add(parse("class X{}"));
        list.add(parse("class X{}"));
        Set<CompilationUnit> set = new VisitorSet<>(new ObjectIdentityHashCodeVisitor(),
                new ObjectIdentityEqualsVisitor());
        set.addAll(list);
        set.add(parse("class X{}"));
        set.retainAll(list);
        assertEquals(2, set.size());
    }

    @Test
    void visitorSetToArray() {
        List<CompilationUnit> list = new ArrayList<>();
        list.add(parse("class X{}"));
        list.add(parse("class X{}"));
        Set<CompilationUnit> set = new VisitorSet<>(new ObjectIdentityHashCodeVisitor(),
                new ObjectIdentityEqualsVisitor());
        set.addAll(list);
        for (CompilationUnit u : set.toArray(new CompilationUnit[2]))
            assertTrue(set.contains(u));
    }
}
