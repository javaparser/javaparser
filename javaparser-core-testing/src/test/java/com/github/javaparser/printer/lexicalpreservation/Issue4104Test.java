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

import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.stmt.BreakStmt;
import com.github.javaparser.ast.stmt.SwitchEntry;
import com.github.javaparser.ast.stmt.SwitchStmt;
import org.junit.jupiter.api.Test;

public class Issue4104Test extends AbstractLexicalPreservingTest {

    @Test
    void test() {
        considerCode("class Foo {\n"
                + "  void foo() {\n"
                + "    switch(bar) {\n"
                + "      default:\n"
                + "        break;\n"
                + "    }\n"
                + "  }\n"
                + "}");
        // should be this
        //		String expected =
        //				"class Foo {\n"
        //				+ "  void foo() {\n"
        //				+ "    switch(bar) {\n"
        //				+ "      default:\n"
        //				+ "        break;\n"
        //				+ "      case 0:\n"
        //				+ "          break;\n"
        //				+ "    }\n"
        //				+ "  }\n"
        //				+ "}";

        String expected = "class Foo {\n"
                + "  void foo() {\n"
                + "    switch(bar) {\n"
                + "      default:\n"
                + "        break;\n"
                + "      case 0:\n"
                + "          break;\n"
                + "      }\n"
                + "  }\n"
                + "}";

        SwitchStmt switchStmt =
                cu.findAll(SwitchStmt.class).stream().findFirst().get();

        SwitchEntry newEntry = new SwitchEntry();
        newEntry.setLabels(NodeList.nodeList(new IntegerLiteralExpr(0)));
        newEntry.setStatements(NodeList.nodeList(new BreakStmt()));
        switchStmt.getEntries().addLast(newEntry);

        assertEqualsStringIgnoringEol(expected, LexicalPreservingPrinter.print(cu));
    }
}
