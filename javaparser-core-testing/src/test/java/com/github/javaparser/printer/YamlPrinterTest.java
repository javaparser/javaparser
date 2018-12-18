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

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.Expression;
import org.junit.Test;

import static com.github.javaparser.utils.TestUtils.assertEqualsNoEol;
import static com.github.javaparser.utils.TestUtils.readTextResource;
import static org.junit.Assert.assertEquals;

public class YamlPrinterTest {

    private String read(String filename) {
        return readTextResource(YamlPrinterTest.class, filename);
    }

    @Test
    public void testWithType() {
        YamlPrinter yamlPrinter = new YamlPrinter(true);
        Expression expression = JavaParser.parseExpression("x(1,1)");
        String output = yamlPrinter.output(expression);
        assertEquals(read("yamlWithType.yaml"), output);
    }

    @Test
    public void testWithoutType() {
        YamlPrinter yamlPrinter = new YamlPrinter(false);
        Expression expression = JavaParser.parseExpression("1+1");
        String output = yamlPrinter.output(expression);
        assertEquals(read("yamlWithoutType.yaml"), output);
    }

    @Test
    public void testWithColonFollowedBySpaceInValue() {
        YamlPrinter yamlPrinter = new YamlPrinter(true);
        Expression expression = JavaParser.parseExpression("\"a\\\\: b\"");
        String output = yamlPrinter.output(expression);
        assertEquals(read("yamlWithColonFollowedBySpaceInValue.yaml"), output);
    }

    @Test
    public void testWithColonFollowedByLineSeparatorInValue() {
        YamlPrinter yamlPrinter = new YamlPrinter(true);
        Expression expression = JavaParser.parseExpression("\"a\\\\:\\\\nb\"");
        String output = yamlPrinter.output(expression);
        assertEquals(read("yamlWithColonFollowedByLineSeparatorInValue.yaml"), output);
    }

    @Test
    public void testParsingJavadocWithQuoteAndNewline() {
        String code = "/**" + System.lineSeparator() +
                " * \" this comment contains a quote and newlines" + System.lineSeparator() +
                " */" + System.lineSeparator() +
                "public class Dog {" + System.lineSeparator() +
                "" + System.lineSeparator() +
                "}";

        YamlPrinter yamlPrinter = new YamlPrinter(true);
        CompilationUnit computationUnit = JavaParser.parse(code);
        String output = yamlPrinter.output(computationUnit);
        assertEquals(read("yamlParsingJavadocWithQuoteAndNewline.yaml"), output);
    }
}
