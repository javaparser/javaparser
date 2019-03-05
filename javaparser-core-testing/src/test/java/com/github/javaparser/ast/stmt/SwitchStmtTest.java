package com.github.javaparser.ast.stmt;

import com.github.javaparser.ast.NodeList;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.parseStatement;
import static com.github.javaparser.ast.stmt.SwitchEntry.Type.EXPRESSION;
import static com.github.javaparser.ast.stmt.SwitchEntry.Type.STATEMENT_GROUP;
import static org.junit.jupiter.api.Assertions.*;

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