/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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

import com.github.javaparser.ast.body.VariableDeclarator;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.utils.TestUtils.assertEqualsStringIgnoringEol;

public class Issue3721Test extends AbstractLexicalPreservingTest {

    @Test
    void issue3721() {
        considerCode(
                "public class Bug {\n"
                + "    public static void main(String[] args) {\n"
                + "        Object msg;\n"
                + "    }\n"
                + "}\n");
        
        String expected =
                "public class Bug {\n"
                + "\n"
                + "    public static void main(String[] args) {\n"
                + "        boolean msg;\n"
                + "    }\n"
                + "}\n";
                

        VariableDeclarator var = cu.findFirst(VariableDeclarator.class).get();
        var.setType("boolean");
        assertEqualsStringIgnoringEol(expected, cu.toString());
    }
}
