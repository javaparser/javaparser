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

package com.github.javaparser.ast.stmt;

import com.github.javaparser.ast.NodeList;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.parseStatement;
import static com.github.javaparser.ast.stmt.SwitchEntry.Type.EXPRESSION;
import static com.github.javaparser.ast.stmt.SwitchEntry.Type.STATEMENT_GROUP;
import static org.junit.jupiter.api.Assertions.assertEquals;

class SwitchStmtTest {
    @Test
    void classicSwitch() {
        SwitchStmt switchStmt = parseStatement("switch (day) {\n" +
                "    case TUESDAY: System.out.println(7); break;\n" +
                "    case FRIDAY: System.out.println(8); break;\n" +
                "    default: System.out.println(-1); \n" +
                "}").asSwitchStmt();

        assertEquals(STATEMENT_GROUP, switchStmt.getEntry(0).getType());
        assertEquals(STATEMENT_GROUP, switchStmt.getEntry(1).getType());
        assertEquals(STATEMENT_GROUP, switchStmt.getEntry(2).getType());
        assertEquals(new NodeList<>(), switchStmt.getEntry(2).getLabels());
    }
    @Test
    void jep325Example1() {
        SwitchStmt switchStmt = parseStatement("switch (day) {\n" +
//                "    case MONDAY, FRIDAY, SUNDAY -> System.out.println(6);\n" +
                "    case TUESDAY                -> System.out.println(7);\n" +
//                "    case THURSDAY, SATURDAY     -> System.out.println(8);\n" +
                "    case WEDNESDAY              -> System.out.println(9);\n" +
                "}").asSwitchStmt();

        assertEquals(EXPRESSION, switchStmt.getEntry(0).getType());
    }



}
