/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2019 The JavaParser Team.
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

import com.github.javaparser.ast.expr.Name;
import org.junit.jupiter.api.Test;

import java.util.Optional;

import static com.github.javaparser.ast.NodeList.nodeList;
import static org.junit.jupiter.api.Assertions.*;

class NodeListTest {

    @Test
    void replace() {
        final NodeList<Name> list = nodeList(new Name("a"), new Name("b"), new Name("c"));

        final boolean replaced = list.replace(new Name("b"), new Name("z"));

        assertTrue(replaced);
        assertEquals(3, list.size());
        assertEquals("a", list.get(0).asString());
        assertEquals("z", list.get(1).asString());
        assertEquals("c", list.get(2).asString());
    }

    @Test
    void toStringTest() {
        final NodeList<Name> list = nodeList(new Name("abc"), new Name("bcd"), new Name("cde"));

        assertEquals(3, list.size());
        assertEquals("[abc, bcd, cde]", list.toString());
    }

    @Test
    void addFirst() {
        final NodeList<Name> list = nodeList(new Name("abc"), new Name("bcd"), new Name("cde"));

        list.addFirst(new Name("xxx"));

        assertEquals(4, list.size());
        assertEquals("[xxx, abc, bcd, cde]", list.toString());
    }

    @Test
    void addLast() {
        final NodeList<Name> list = nodeList(new Name("abc"), new Name("bcd"), new Name("cde"));

        list.addLast(new Name("xxx"));

        assertEquals(4, list.size());
        assertEquals("[abc, bcd, cde, xxx]", list.toString());
    }

    @Test
    void addBefore() {
        Name n = new Name("bcd");
        final NodeList<Name> list = nodeList(new Name("abc"), n, new Name("cde"));

        list.addBefore(new Name("xxx"), n);

        assertEquals(4, list.size());
        assertEquals("[abc, xxx, bcd, cde]", list.toString());
    }

    @Test
    void addAfter() {
        Name n = new Name("bcd");
        final NodeList<Name> list = nodeList(new Name("abc"), n, new Name("cde"));

        list.addAfter(new Name("xxx"), n);

        assertEquals(4, list.size());
        assertEquals("[abc, bcd, xxx, cde]", list.toString());
    }

    @Test
    void addBeforeFirst() {
        Name abc = new Name("abc");
        final NodeList<Name> list = nodeList(abc, new Name("bcd"), new Name("cde"));

        list.addBefore(new Name("xxx"), abc);

        assertEquals(4, list.size());
        assertEquals("[xxx, abc, bcd, cde]", list.toString());
    }

    @Test
    void addAfterLast() {
        Name cde = new Name("cde");
        final NodeList<Name> list = nodeList(new Name("abc"), new Name("bcd"), cde);

        list.addAfter(new Name("xxx"), cde);

        assertEquals(4, list.size());
        assertEquals("[abc, bcd, cde, xxx]", list.toString());
    }


    @Test
    public void getFirstWhenEmpty() {
        final NodeList<Name> list = nodeList();

        Optional<Name> first = list.getFirst();

        assertFalse(first.isPresent());
        assertEquals("Optional.empty", first.toString());
    }

    @Test
    public void getFirstWhenNonEmpty() {
        final NodeList<Name> list = nodeList(new Name("abc"), new Name("bcd"), new Name("cde"));

        Optional<Name> first = list.getFirst();

        assertTrue(first.isPresent());
        assertEquals("Optional[abc]", first.toString());
    }
    @Test
    public void getLastWhenEmpty() {
        final NodeList<Name> list = nodeList();

        Optional<Name> last = list.getLast();

        assertFalse(last.isPresent());
        assertEquals("Optional.empty", last.toString());
    }

    @Test
    public void getLastWhenNonEmpty() {
        final NodeList<Name> list = nodeList(new Name("abc"), new Name("bcd"), new Name("cde"));

        Optional<Name> last = list.getLast();

        assertTrue(last.isPresent());
        assertEquals("Optional[cde]", last.toString());
    }
}
