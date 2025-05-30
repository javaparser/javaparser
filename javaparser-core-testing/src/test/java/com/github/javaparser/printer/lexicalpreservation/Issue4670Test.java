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

import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import org.junit.jupiter.api.Test;

public class Issue4670Test extends AbstractLexicalPreservingTest {

    @Test
    void test() {
        // A parameter with an annotation and a final modifier
        final String code = "public interface Foo {\n" + "  void bar(final @PathVariable(\"id\") String id);\n" + "}";
        considerCode(code);
        LexicalPreservingPrinter.setup(cu);

        // Remove the final modifier from parameters.
        cu.accept(
                new VoidVisitorAdapter<Void>() {
                    @Override
                    public void visit(Parameter p, Void arg) {
                        p.setFinal(false);
                    }
                },
                null);

        String actual = LexicalPreservingPrinter.print(cu);
        String expected = "public interface Foo {\n" + "  void bar(@PathVariable(\"id\") String id);\n" + "}";

        assertEqualsStringIgnoringEol(expected, actual);
    }
}
