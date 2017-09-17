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

public class YamlPrinterTest {

    @Test
    public void testWithType() {
        String expectedOutput = "---" + System.lineSeparator();
        expectedOutput += "root(Type=MethodCallExpr): " + System.lineSeparator();
        expectedOutput += "    name(Type=SimpleName): " + System.lineSeparator();
        expectedOutput += "        identifier: x" + System.lineSeparator();
        expectedOutput += "    arguments: " + System.lineSeparator();
        expectedOutput += "        - argument(Type=IntegerLiteralExpr): " + System.lineSeparator();
        expectedOutput += "            value: 1" + System.lineSeparator();
        expectedOutput += "        - argument(Type=IntegerLiteralExpr): " + System.lineSeparator();
        expectedOutput += "            value: 1" + System.lineSeparator();
        expectedOutput += "...";

        YamlPrinter YamlPrinter = new YamlPrinter(true);
        Expression expression = JavaParser.parseExpression("x(1,1)");
        String output = YamlPrinter.output(expression);
        assertEquals(expectedOutput, output);
    }

    @Test
    public void testWithoutType() {
        String expectedOutput = "---" + System.lineSeparator();
        expectedOutput += "root: " + System.lineSeparator();
        expectedOutput += "    operator: PLUS" + System.lineSeparator();
        expectedOutput += "    left: " + System.lineSeparator();
        expectedOutput += "        value: 1" + System.lineSeparator();
        expectedOutput += "    right: " + System.lineSeparator();
        expectedOutput += "        value: 1" + System.lineSeparator();
        expectedOutput += "...";

        YamlPrinter YamlPrinter = new YamlPrinter(false);
        Expression expression = JavaParser.parseExpression("1+1");
        String output = YamlPrinter.output(expression);
        assertEquals(expectedOutput, output);
    }
}
