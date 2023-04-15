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

import com.github.javaparser.ParseProblemException;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.parseExpression;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

class SuperExprTest {
    @Test
    void justSuper() {
        assertThrows(ParseProblemException.class, () -> parseExpression("super"));
    }

    @Test
    void singleScopeSuper() {
        Expression expr = parseExpression("A.super");

        Name className = expr.asSuperExpr().getTypeName().get();

        assertEquals("A", className.asString());
    }

    @Test
    void multiScopeSuper() {
        Expression expr = parseExpression("a.B.super");

        Name className = expr.asSuperExpr().getTypeName().get();

        assertEquals("a.B", className.asString());
    }
}
