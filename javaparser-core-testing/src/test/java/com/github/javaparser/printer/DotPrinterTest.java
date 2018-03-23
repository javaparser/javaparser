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

package com.github.javaparser.printer;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.expr.Expression;

public class DotPrinterTest {
    @Test
    public void testWithType() {
        String expectedOutput = "digraph {" + System.lineSeparator();
        expectedOutput += "n0 [label=\"root (MethodCallExpr)\"];" + System.lineSeparator();
        expectedOutput += "n1 [label=\"name (SimpleName)\"];" + System.lineSeparator();
        expectedOutput += "n0 -> n1;" + System.lineSeparator();
        expectedOutput += "n2 [label=\"identifier='x'\"];" + System.lineSeparator();
        expectedOutput += "n1 -> n2;" + System.lineSeparator();
        expectedOutput += "n3 [label=\"arguments\"];" + System.lineSeparator();
        expectedOutput += "n0 -> n3;" + System.lineSeparator();
        expectedOutput += "n4 [label=\"argument (IntegerLiteralExpr)\"];" + System.lineSeparator();
        expectedOutput += "n3 -> n4;" + System.lineSeparator();
        expectedOutput += "n5 [label=\"value='1'\"];" + System.lineSeparator();
        expectedOutput += "n4 -> n5;" + System.lineSeparator();
        expectedOutput += "n6 [label=\"argument (IntegerLiteralExpr)\"];" + System.lineSeparator();
        expectedOutput += "n3 -> n6;" + System.lineSeparator();
        expectedOutput += "n7 [label=\"value='1'\"];" + System.lineSeparator();
        expectedOutput += "n6 -> n7;" + System.lineSeparator();
        expectedOutput += "}";

        DotPrinter dotPrinter = new DotPrinter(true);
        Expression expression = JavaParser.parseExpression("x(1,1)");
        String output = dotPrinter.output(expression);
        assertEquals(expectedOutput, output);
    }

    @Test
    public void testWithoutType() {
        String expectedOutput = "digraph {" + System.lineSeparator();
        expectedOutput += "n0 [label=\"root\"];" + System.lineSeparator();
        expectedOutput += "n1 [label=\"operator='PLUS'\"];" + System.lineSeparator();
        expectedOutput += "n0 -> n1;" + System.lineSeparator();
        expectedOutput += "n2 [label=\"left\"];" + System.lineSeparator();
        expectedOutput += "n0 -> n2;" + System.lineSeparator();
        expectedOutput += "n3 [label=\"value='1'\"];" + System.lineSeparator();
        expectedOutput += "n2 -> n3;" + System.lineSeparator();
        expectedOutput += "n4 [label=\"right\"];" + System.lineSeparator();
        expectedOutput += "n0 -> n4;" + System.lineSeparator();
        expectedOutput += "n5 [label=\"value='1'\"];" + System.lineSeparator();
        expectedOutput += "n4 -> n5;" + System.lineSeparator();
        expectedOutput += "}";

        DotPrinter dotPrinter = new DotPrinter(false);
        Expression expression = JavaParser.parseExpression("1+1");
        String output = dotPrinter.output(expression);
        assertEquals(expectedOutput, output);
    }
}
