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

package com.github.javaparser.ast.expr;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.parseExpression;

class DoubleLiteralExprTest {
    @Test
    void test1() {
        float x = 0x0.00_00_02p-126f;
        DoubleLiteralExpr e = parseExpression("0x0.00_00_02p-126f");
        Assertions.assertEquals(x, e.asDouble());
    }

    @Test
    void test2() {
        double x = 0x0.000_000_000_000_1p-1_022;
        DoubleLiteralExpr e = parseExpression("0x0.000_000_000_000_1p-1_022");
        Assertions.assertEquals(x, e.asDouble());
    }

    @Test
    void test3() {
        double a = 0x1.p+1;
        DoubleLiteralExpr e = parseExpression("0x1.p+1");
        Assertions.assertEquals(a, e.asDouble());
    }

    @Test
    void test4() {
        double a = 0x.0p0;
        DoubleLiteralExpr e = parseExpression("0x.0p0");
        Assertions.assertEquals(a, e.asDouble());
    }

    @Test
    void test5() {
        double x = 0x0_0.0_0p-1_0;
        DoubleLiteralExpr e = parseExpression("0x0_0.0_0p-1_0");
        Assertions.assertEquals(x, e.asDouble());
    }
}
