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

package com.github.javaparser.printer.lexicalpreservation;

import static com.github.javaparser.utils.TestUtils.assertEqualsStringIgnoringEol;
import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.ast.body.MethodDeclaration;
import org.junit.jupiter.api.Test;

class Issue5099Test extends AbstractLexicalPreservingTest {

    @Test
    void setJavadocCommentReplacesSingleLineMarkdownComment() {
        considerCode("package test;\n" + "public class Error\n"
                + "{\n"
                + "  /// dummy.\n"
                + "  public void x()\n"
                + "  { }\n"
                + "}\n");

        MethodDeclaration method = cu.findFirst(MethodDeclaration.class).get();
        method.setJavadocComment(" replacement");

        assertEqualsStringIgnoringEol(
                "package test;\n" + "public class Error\n"
                        + "{\n"
                        + "  /** replacement*/\n"
                        + "  public void x()\n"
                        + "  { }\n"
                        + "}\n",
                LexicalPreservingPrinter.print(cu));
    }

    @Test
    void removeJavaDocCommentKeepsMethodWithSingleLineMarkdownComment() {
        considerCode("package test;\n" + "public class Error\n"
                + "{\n"
                + "  /// dummy.\n"
                + "  public void x()\n"
                + "  { }\n"
                + "}\n");

        MethodDeclaration method = cu.findFirst(MethodDeclaration.class).get();
        assertTrue(method.removeJavaDocComment());

        assertEqualsStringIgnoringEol(
                "package test;\n" + "public class Error\n" + "{\n" + "  public void x()\n" + "  { }\n" + "}\n",
                LexicalPreservingPrinter.print(cu));
    }
}
