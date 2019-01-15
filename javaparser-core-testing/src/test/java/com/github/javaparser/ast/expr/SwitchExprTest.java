package com.github.javaparser.ast.expr;

import com.github.javaparser.JavaParser;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

class SwitchExprTest {
    @Test
    void jep325Example1() {
        JavaParser.parseStatement("switch (day) {\n" +
//                "    case MONDAY, FRIDAY, SUNDAY -> System.out.println(6);\n" +
                "    case TUESDAY                -> System.out.println(7);\n" +
//                "    case THURSDAY, SATURDAY     -> System.out.println(8);\n" +
                "    case WEDNESDAY              -> System.out.println(9);\n" +
                "}");
    }

    @Test
    void jep325Example2() {
        JavaParser.parseStatement("int numLetters = switch (day) {\n" +
//                "    case MONDAY, FRIDAY, SUNDAY -> 6;\n" +
                "    case TUESDAY                -> 7;\n" +
//                "    case THURSDAY, SATURDAY     -> 8;\n" +
                "    case WEDNESDAY              -> 9;\n" +
                "};");
    }

    @Test
    void jep325Example3() {
        JavaParser.parseBodyDeclaration("static void howMany(int k) {\n" +
                "    switch (k) {\n" +
                "        case 1 -> System.out.println(\"one\");\n" +
                "        case 2 -> System.out.println(\"two\");\n" +
                "        case 3 -> System.out.println(\"many\");\n" +
                "    }\n" +
                "}");
    }

    @Test
    void jep325Example4() {
        JavaParser.parseStatement("T result = switch (arg) {\n" +
                "    case L1 -> e1;\n" +
                "    case L2 -> e2;\n" +
                "    default -> e3;\n" +
                "};");
    }

    @Test
    void jep325Example5() {
        JavaParser.parseStatement("int j = switch (day) {\n" +
                "    case MONDAY  -> 0;\n" +
                "    case TUESDAY -> 1;\n" +
                "    default      -> {\n" +
                "        int k = day.toString().length();\n" +
                "        int result = f(k);\n" +
                "        break result;\n" +
                "    }\n" +
                "};");
    }

    @Disabled
    @Test
    void jep325Example6() {
        JavaParser.parseStatement("int result = switch (s) {\n" +
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
