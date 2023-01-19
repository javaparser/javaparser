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

package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.parseExpression;
import static com.github.javaparser.utils.TestUtils.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertFalse;

class NodeWithTraversableScopeTest {
    @Test
    void traverse1() {
        NodeWithTraversableScope expression = parseExpression("getAddress().name.startsWith(\"abc\")");

        assertInstanceOf(MethodCallExpr.class, expression);
        expression = (NodeWithTraversableScope) expression.traverseScope().get();
        assertInstanceOf(FieldAccessExpr.class, expression);
        expression = (NodeWithTraversableScope) expression.traverseScope().get();
        assertInstanceOf(MethodCallExpr.class, expression);
        assertFalse(expression.traverseScope().isPresent());
    }
}
