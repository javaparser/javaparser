package com.github.javaparser.ast.expr;

import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.SwitchEntry;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.ast.stmt.SwitchEntry.Type.*;
import static com.github.javaparser.utils.TestParser.*;
import static org.junit.jupiter.api.Assertions.assertEquals;

class SwitchExprTest {
    @Test
    void jep325Example2() {
        NodeList<Expression> entry2labels = parseStatement("int numLetters = switch (day) {\n" +
                "    case MONDAY, FRIDAY, SUNDAY -> 6;\n" +
                "    case TUESDAY                -> 7;\n" +
                "    case THURSDAY, SATURDAY     -> 8;\n" +
                "    case WEDNESDAY              -> 9;\n" +
                "};").findAll(SwitchEntry.class).get(0).getLabels();

        assertEquals(3, entry2labels.size());
        assertEquals("MONDAY", entry2labels.get(0).toString());
        assertEquals("FRIDAY", entry2labels.get(1).toString());
        assertEquals("SUNDAY", entry2labels.get(2).toString());
    }

    @Test
    void funkyExpressions() {
        parseStatement("int numLetters = switch (day) {\n" +
                "    case 1+1, 2+2 -> 6;\n" +
                "    case \"Henk\"-> 7;\n" +
                "    case ((3)+3)+3 -> 8;\n" +
                "};");
    }

    @Test
    void jep325Example3() {
        parseBodyDeclaration("static void howMany(int k) {\n" +
                "    switch (k) {\n" +
                "        case 1 -> System.out.println(\"one\");\n" +
                "        case 2 -> System.out.println(\"two\");\n" +
                "        case 3 -> System.out.println(\"many\");\n" +
                "    }\n" +
                "}");
    }


    @Test
    void aThrowStatement() {
        SwitchExpr switchExpr = parseExpression("switch (k) {\n" +
                "        case 1 -> throw new Exception(\"one\");\n" +
                "    }").findFirst(SwitchExpr.class).get();

        assertEquals(THROWS_STATEMENT, switchExpr.getEntry(0).getType());
    }

    @Test
    void jep325Example4() {
        SwitchExpr switchExpr = parseStatement("T result = switch (arg) {\n" +
                "    case L1 -> e1;\n" +
                "    case L2 -> e2;\n" +
                "    default -> e3;\n" +
                "};").findFirst(SwitchExpr.class).get();

        assertEquals(EXPRESSION, switchExpr.getEntry(0).getType());
    }

    @Test
    void jep325Example5() {
        SwitchExpr switchExpr = parseStatement("int j = switch (day) {\n" +
                "    case MONDAY  -> 0;\n" +
                "    case TUESDAY -> 1;\n" +
                "    default      -> {\n" +
                "        int k = day.toString().length();\n" +
                "        int result = f(k);\n" +
                "        break result;\n" +
                "    }\n" +
                "};").findFirst(SwitchExpr.class).get();

        assertEquals(BLOCK, switchExpr.getEntry(2).getType());
        assertEquals(BlockStmt.class, switchExpr.getEntry(2).getStatements().get(0).getClass());
    }

    @Test
    void jep325Example6() {
        parseStatement("int result = switch (s) {\n" +
                "    case \"Foo\": \n" +
                "        break 1;\n" +
                "    case \"Bar\":\n" +
                "        break 2;\n" +
                "    default:\n" +
                "        System.out.println(\"Neither Foo nor Bar, hmmm...\");\n" +
                "        break 0;\n" +
                "};");
    }
}
