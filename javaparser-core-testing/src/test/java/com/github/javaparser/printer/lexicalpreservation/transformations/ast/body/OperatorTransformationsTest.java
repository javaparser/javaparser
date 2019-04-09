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

package com.github.javaparser.printer.lexicalpreservation.transformations.ast.body;

import java.io.IOException;

import org.junit.jupiter.api.Test;

import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.printer.lexicalpreservation.AbstractLexicalPreservingTest;

/**
 * Transforming BinaryExpr and verifying the LexicalPreservation works as expected.
 */
class OperatorTransformationsTest extends AbstractLexicalPreservingTest {

    @Test
    void binaryExpressionOperator() {
        considerExpression("a && b");
        expression.asBinaryExpr().setRight(new NameExpr("c"));
        assertTransformedToString("a && c", expression);
    }
    
    @Test
    void unaryExpressionOperator() {
        considerExpression("!a");
        expression.asUnaryExpr().setExpression(new NameExpr("b"));
        assertTransformedToString("!b", expression);
    }
    
    @Test
    void assignExpressionOperator() {
        considerExpression("a <<= 1");
        expression.asAssignExpr().setValue(new IntegerLiteralExpr(2));
        assertTransformedToString("a <<= 2", expression);
    }

}
