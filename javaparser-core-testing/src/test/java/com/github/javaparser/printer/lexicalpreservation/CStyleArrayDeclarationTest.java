/*
 * Copyright (C) 2013-2026 The JavaParser Team.
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

package com.github.javaparser.printer.lexicalpreservation;

import static org.junit.jupiter.api.Assertions.assertEquals;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.nodeTypes.NodeWithSimpleName;
import com.github.javaparser.ast.nodeTypes.NodeWithType;
import com.github.javaparser.ast.type.ArrayType;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.ast.type.Type;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;

/**
 * Changes of the name or of the type of a declaration whose array brackets are written after the name
 * ({@code int a[]}, "C-style" array declaration), printed with the lexical preserving printer.
 * <p>
 * The declaration changed is always the parameter or variable named {@code a}.
 */
class CStyleArrayDeclarationTest extends AbstractLexicalPreservingTest {

    /**
     * Renaming the declared variable keeps the brackets after the new name.
     */
    @ParameterizedTest
    @CsvSource(
            delimiter = '|',
            value = {
                "class A { void m(String a[]) {} }         | class A { void m(String b[]) {} }",
                "class A { void m(String a[][]) {} }       | class A { void m(String b[][]) {} }",
                "class A { void m(String[] a[]) {} }       | class A { void m(String[] b[]) {} }",
                "class A { void m() { int a[] = null; } }  | class A { void m() { int b[] = null; } }",
                "class A { void m() { int a[], c = 0; } }  | class A { void m() { int b[], c = 0; } }",
                "class A { int a[]; }                      | class A { int b[]; }",
                "class A { int a[][]; }                    | class A { int b[][]; }",
                "class A { int a[], c; }                   | class A { int b[], c; }",
                "class A { int c, a[]; }                   | class A { int c, b[]; }"
            })
    void renameIdentifier(String code, String expected) {
        considerCode(code);

        declarationNamedA().getName().setIdentifier("b");

        assertEquals(expected, LexicalPreservingPrinter.print(cu));
    }

    /**
     * Replacing the name node of the declaration keeps the brackets after the new name.
     */
    @ParameterizedTest
    @CsvSource(
            delimiter = '|',
            value = {
                "class A { void m(String a[]) {} }         | class A { void m(String b[]) {} }",
                "class A { void m() { int a[] = null; } }  | class A { void m() { int b[] = null; } }",
                "class A { void m() { int a[], c = 0; } }  | class A { void m() { int b[], c = 0; } }",
                "class A { int a[][]; }                    | class A { int b[][]; }",
                "class A { int c, a[]; }                   | class A { int c, b[]; }"
            })
    void replaceName(String code, String expected) {
        considerCode(code);

        declarationNamedA().setName(new SimpleName("b"));

        assertEquals(expected, LexicalPreservingPrinter.print(cu));
    }

    /**
     * Replacing the type of the declaration by a type without array level removes the brackets after the name: they
     * belonged to the replaced type.
     */
    @ParameterizedTest
    @CsvSource(
            delimiter = '|',
            value = {
                "class A { void m(String a[]) {} }         | class A { void m(long a) {} }",
                "class A { void m(String[] a[]) {} }       | class A { void m(long a) {} }",
                "class A { void m() { int a[] = null; } }  | class A { void m() { long a = null; } }",
                "class A { int a[][]; }                    | class A { long a; }"
            })
    void replaceTypeByNonArrayType(String code, String expected) {
        considerCode(code);

        setType(declarationNamedA(), PrimitiveType.longType());

        assertEquals(expected, LexicalPreservingPrinter.print(cu));
    }

    /**
     * Replacing the type of the declaration by an array type built in code writes its brackets after the element type,
     * the default origin of an {@link ArrayType}.
     */
    @ParameterizedTest
    @CsvSource(
            delimiter = '|',
            value = {
                "class A { void m(String a[][]) {} }       | class A { void m(long[] a) {} }",
                "class A { void m() { int a[] = null; } }  | class A { void m() { long[] a = null; } }",
                "class A { int a[]; }                      | class A { long[] a; }"
            })
    void replaceTypeByArrayType(String code, String expected) {
        considerCode(code);

        setType(declarationNamedA(), new ArrayType(PrimitiveType.longType()));

        assertEquals(expected, LexicalPreservingPrinter.print(cu));
    }

    /**
     * @return the parameter or variable declarator named {@code a} in the code under test
     */
    private NodeWithSimpleName<?> declarationNamedA() {
        return (NodeWithSimpleName<?>) cu.findFirst(
                        Node.class,
                        n -> (n instanceof Parameter || n instanceof VariableDeclarator)
                                && ((NodeWithSimpleName<?>) n).getNameAsString().equals("a"))
                .get();
    }

    @SuppressWarnings({"unchecked", "rawtypes"})
    private static void setType(NodeWithSimpleName<?> declaration, Type type) {
        ((NodeWithType) declaration).setType(type);
    }
}
