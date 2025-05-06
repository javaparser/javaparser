/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2024 The JavaParser Team.
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

import static com.github.javaparser.utils.TestUtils.assertEqualsStringIgnoringEol;

import com.github.javaparser.ast.expr.MarkerAnnotationExpr;
import com.github.javaparser.ast.visitor.ModifierVisitor;
import com.github.javaparser.ast.visitor.Visitable;
import org.junit.jupiter.api.Test;

public class Issue4747Test extends AbstractLexicalPreservingTest {

    @Test
    void test() {
        final String code = "public class TestClass {\n"
                + "    @com.abc.def.TestMarkerAnnotation\n"
                + "    public void method1() {}\n"
                + "}";
        considerCode(code);
        cu.accept(
                new ModifierVisitor<Void>() {
                    public Visitable visit(final MarkerAnnotationExpr expr, final Void arg) {
                        if (expr.getNameAsString().equals("com.abc.def.TestMarkerAnnotation")) {
                            expr.setName("TestMarkerAnnotation");
                        }

                        return super.visit(expr, arg);
                    }
                },
                null);

        String actual = LexicalPreservingPrinter.print(cu);
        String expected =
                "public class TestClass {\n" + "    @TestMarkerAnnotation\n" + "    public void method1() {}\n" + "}";

        assertEqualsStringIgnoringEol(expected, actual);
    }
}
