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

package com.github.javaparser.ast.visitor;

import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.StringLiteralExpr;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class ModifierVisitorTest {
    @Test
    public void x() {
        NodeList<StringLiteralExpr> list = new NodeList<>();
        list.add(new StringLiteralExpr("a"));
        list.add(new StringLiteralExpr("b"));
        list.add(new StringLiteralExpr("c"));

        list.accept(new ModifierVisitor<Void>() {
            @Override
            public Visitable visit(final StringLiteralExpr n, final Void arg) {
                String v = n.getValue();

                list.add(new StringLiteralExpr("extra " + v));

                if (v.equals("a")) {
                    return new StringLiteralExpr("x");
                }
                if (v.equals("b")) {
                    return null;
                }

                return n;
            }
        }, null);

        assertEquals("x", list.get(0).getValue());
        assertEquals("c", list.get(1).getValue());
        assertEquals("extra a", list.get(2).getValue());
        assertEquals("extra b", list.get(3).getValue());
        assertEquals("extra c", list.get(4).getValue());
        assertEquals(5, list.size());
    }
}
