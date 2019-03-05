/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2016 The JavaParser Team.
 *
 * This file is part of 
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

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.Expression;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.parse;
import static com.github.javaparser.StaticJavaParser.parseExpression;
import static com.github.javaparser.utils.TestUtils.assertEqualsNoEol;
import static com.github.javaparser.utils.TestUtils.readTextResource;

class YamlPrinterTest {

    private String read(String filename) {
        return readTextResource(YamlPrinterTest.class, filename);
    }

    @Test
    void testWithType() {
        YamlPrinter yamlPrinter = new YamlPrinter(true);
        Expression expression = parseExpression("x(1,1)");
        String output = yamlPrinter.output(expression);
        assertEqualsNoEol(read("yamlWithType.yaml"), output);
    }

    @Test
    void testWithoutType() {
        YamlPrinter yamlPrinter = new YamlPrinter(false);
        Expression expression = parseExpression("1+1");
        String output = yamlPrinter.output(expression);
        assertEqualsNoEol(read("yamlWithoutType.yaml"), output);
    }

    @Test
    void testWithColonFollowedBySpaceInValue() {
        YamlPrinter yamlPrinter = new YamlPrinter(true);
        Expression expression = parseExpression("\"a\\\\: b\"");
        String output = yamlPrinter.output(expression);
        assertEqualsNoEol(read("yamlWithColonFollowedBySpaceInValue.yaml"), output);
    }

    @Test
    void testWithColonFollowedByLineSeparatorInValue() {
        YamlPrinter yamlPrinter = new YamlPrinter(true);
        Expression expression = parseExpression("\"a\\\\:\\\\nb\"");
        String output = yamlPrinter.output(expression);
        assertEqualsNoEol(read("yamlWithColonFollowedByLineSeparatorInValue.yaml"), output);
    }

    @Test
    void testParsingJavadocWithQuoteAndNewline() {
        String code = "/**\n" + 
                " * \" this comment contains a quote and newlines\n" +
                " */\n" + 
                "public class Dog {}";

        YamlPrinter yamlPrinter = new YamlPrinter(true);
        CompilationUnit computationUnit = parse(code);
        String output = yamlPrinter.output(computationUnit);
        assertEqualsNoEol(read("yamlParsingJavadocWithQuoteAndNewline.yaml"), output);
    }
}
