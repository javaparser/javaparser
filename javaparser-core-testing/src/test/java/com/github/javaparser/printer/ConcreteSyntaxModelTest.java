/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2026 The JavaParser Team.
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

import static org.junit.jupiter.api.Assertions.assertEquals;

import com.github.javaparser.JavaParserAdapter;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.ClassExpr;
import com.github.javaparser.utils.LineSeparator;
import org.junit.jupiter.api.Test;

class ConcreteSyntaxModelTest {

    private final JavaParserAdapter parser = StaticJavaParser.newParserAdapter();

    private String print(Node node) {
        return ConcreteSyntaxModel.genericPrettyPrint(node);
    }

    @Test
    void printSimpleClassExpr() {
        ClassExpr expr = parser.parseExpression("Foo.class");
        assertEquals("Foo.class", print(expr));
    }

    @Test
    void printArrayClassExpr() {
        ClassExpr expr = parser.parseExpression("Foo[].class");
        assertEquals("Foo[].class", print(expr));
    }

    @Test
    void printGenericClassExpr() {
        ClassExpr expr = parser.parseExpression("Foo<String>.class");
        assertEquals("Foo<String>.class", print(expr));
    }

    @Test
    void printSimplestClass() {
        Node node = parser.parse("class A {}");
        assertEquals("class A {" + LineSeparator.SYSTEM + "}" + LineSeparator.SYSTEM, print(node));
    }

    @Test
    void printAClassWithField() {
        Node node = parser.parse("class A { int a; }");
        assertEquals(
                "class A {" + LineSeparator.SYSTEM
                        + LineSeparator.SYSTEM + "    int a;"
                        + LineSeparator.SYSTEM + "}"
                        + LineSeparator.SYSTEM,
                print(node));
    }

    @Test
    void printParameters() {
        Node node = parser.parseBodyDeclaration("int x(int y, int z) {}");
        assertEquals("int x(int y, int z) {" + LineSeparator.SYSTEM + "}", print(node));
    }

    @Test
    void printReceiverParameter() {
        Node node = parser.parseBodyDeclaration("int x(X A.B.this, int y, int z) {}");
        assertEquals("int x(X A.B.this, int y, int z) {" + LineSeparator.SYSTEM + "}", print(node));
    }

    @Test
    void printAnEmptyInterface() {
        Node node = parser.parse("interface A {}");
        assertEquals("interface A {" + LineSeparator.SYSTEM + "}" + LineSeparator.SYSTEM, print(node));
    }

    @Test
    void printAnEmptyInterfaceWithModifier() {
        Node node = parser.parse("public interface A {}");
        assertEquals("public interface A {" + LineSeparator.SYSTEM + "}" + LineSeparator.SYSTEM, print(node));
    }
}
