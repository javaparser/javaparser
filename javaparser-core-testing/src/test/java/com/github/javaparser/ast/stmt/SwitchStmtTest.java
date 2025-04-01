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

package com.github.javaparser.ast.stmt;

import static com.github.javaparser.StaticJavaParser.parseStatement;
import static com.github.javaparser.ast.stmt.SwitchEntry.Type.EXPRESSION;
import static com.github.javaparser.ast.stmt.SwitchEntry.Type.STATEMENT_GROUP;
import static org.junit.jupiter.api.Assertions.*;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.NullLiteralExpr;
import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

class SwitchStmtTest {

    private static final ParserConfiguration.LanguageLevel storedLanguageLevel =
            StaticJavaParser.getParserConfiguration().getLanguageLevel();

    @BeforeAll
    public static void setLanguageLevel() {
        StaticJavaParser.getParserConfiguration().setLanguageLevel(ParserConfiguration.LanguageLevel.BLEEDING_EDGE);
    }

    @AfterAll
    public static void resetLanguageLevel() {
        StaticJavaParser.getParserConfiguration().setLanguageLevel(storedLanguageLevel);
    }

    @Test
    void classicSwitch() {
        SwitchStmt switchStmt = parseStatement("switch (day) {\n" + "    case TUESDAY: System.out.println(7); break;\n"
                        + "    case FRIDAY: System.out.println(8); break;\n"
                        + "    default: System.out.println(-1); \n"
                        + "}")
                .asSwitchStmt();

        assertEquals(STATEMENT_GROUP, switchStmt.getEntry(0).getType());
        assertEquals(STATEMENT_GROUP, switchStmt.getEntry(1).getType());
        assertEquals(STATEMENT_GROUP, switchStmt.getEntry(2).getType());
        assertEquals(new NodeList<>(), switchStmt.getEntry(2).getLabels());
        assertFalse(switchStmt.getEntry(0).isDefault());
        assertFalse(switchStmt.getEntry(1).isDefault());
        assertTrue(switchStmt.getEntry(2).isDefault());
    }

    @Test
    void jep325Example1() {
        SwitchStmt switchStmt = parseStatement("switch (day) {\n" +
                        //                "    case MONDAY, FRIDAY, SUNDAY -> System.out.println(6);\n" +
                        "    case TUESDAY                -> System.out.println(7);\n"
                        +
                        //                "    case THURSDAY, SATURDAY     -> System.out.println(8);\n" +
                        "    case WEDNESDAY              -> System.out.println(9);\n"
                        + "}")
                .asSwitchStmt();

        assertEquals(EXPRESSION, switchStmt.getEntry(0).getType());
    }

    @Test
    void jep441Example1() {
        SwitchStmt switchStmt = parseStatement(
                        "switch (day) {\n" + "    case null, default -> System.out.println(-1); \n" + "}")
                .asSwitchStmt();

        assertTrue(switchStmt.getEntry(0).isDefault());
        assertInstanceOf(
                NullLiteralExpr.class, switchStmt.getEntry(0).getLabels().get(0));
    }

    @Test
    void issue4455Test() {
        SwitchStmt switchStmt = parseStatement(
                        "switch (column) {\n" + "  case CustomDeployTableModel.ARTIFACT_NAME:\n" + "}")
                .asSwitchStmt();

        assertEquals(Node.Parsedness.PARSED, switchStmt.getParsed());

        SwitchEntry entry = switchStmt.getEntry(0);
        Expression switchLabel = entry.getLabels().get(0);

        assertEquals("CustomDeployTableModel.ARTIFACT_NAME", switchLabel.toString());
        assertTrue(switchLabel.isFieldAccessExpr());
    }

    @Test
    void issue4607Test() {
        SwitchStmt switchStmt = parseStatement("switch (o) { case String s when s.length() == 1 -> 0; }")
                .asSwitchStmt();
        assertEquals(switchStmt.toString(), switchStmt.clone().toString());
    }
}
