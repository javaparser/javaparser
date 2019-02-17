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

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.ClassExpr;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.*;
import static com.github.javaparser.utils.Utils.EOL;
import static org.junit.jupiter.api.Assertions.assertEquals;

class ConcreteSyntaxModelTest {

    private String print(Node node) {
        return ConcreteSyntaxModel.genericPrettyPrint(node);
    }

    @Test
    void printSimpleClassExpr() {
        ClassExpr expr = parseExpression("Foo.class");
        assertEquals("Foo.class", print(expr));
    }

    @Test
    void printArrayClassExpr() {
        ClassExpr expr = parseExpression("Foo[].class");
        assertEquals("Foo[].class", print(expr));
    }

    @Test
    void printGenericClassExpr() {
        ClassExpr expr = parseExpression("Foo<String>.class");
        assertEquals("Foo<String>.class", print(expr));
    }

    @Test
    void printSimplestClass() {
        Node node = parse("class A {}");
        assertEquals("class A {" + EOL +
                "}" + EOL, print(node));
    }

    @Test
    void printAClassWithField() {
        Node node = parse("class A { int a; }");
        assertEquals("class A {" + EOL
                + EOL +
                "    int a;" + EOL +
                "}" + EOL, print(node));
    }

    @Test
    void printParameters() {
        Node node = parseBodyDeclaration("int x(int y, int z) {}");
        assertEquals("int x(int y, int z) {" + EOL + "}", print(node));
    }

    @Test
    void printReceiverParameter() {
        Node node = parseBodyDeclaration("int x(X A.B.this, int y, int z) {}");
        assertEquals("int x(X A.B.this, int y, int z) {" + EOL + "}", print(node));
    }

    @Test
    void printAnEmptyInterface() {
        Node node = parse("interface A {}");
        assertEquals("interface A {" + EOL +
                "}" + EOL, print(node));
    }

    @Test
    void printAnEmptyInterfaceWithModifier() {
        Node node = parse("public interface A {}");
        assertEquals("public interface A {" + EOL +
                "}" + EOL, print(node));
    }
}
