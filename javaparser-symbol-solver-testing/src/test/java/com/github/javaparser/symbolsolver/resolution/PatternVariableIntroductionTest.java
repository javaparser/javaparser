/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2024 The JavaParser Team.
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
package com.github.javaparser.symbolsolver.resolution;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.stmt.SwitchStmt;
import com.github.javaparser.resolution.Navigator;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

/**
 * Tests the rules for variables introduced by patterns as described in
 *   https://docs.oracle.com/javase/specs/jls/se22/html/jls-6.html#jls-6.3.1
 * and
 *   https://docs.oracle.com/javase/specs/jls/se22/html/jls-6.html#jls-6.3.2
 */
public class PatternVariableIntroductionTest {

    private CompilationUnit parse(String code) {
        TypeSolver typeSolver = new ReflectionTypeSolver();
        ParserConfiguration parserConfiguration = new ParserConfiguration();
        parserConfiguration.setSymbolResolver(new JavaSymbolSolver(typeSolver));
        parserConfiguration.setLanguageLevel(ParserConfiguration.LanguageLevel.BLEEDING_EDGE);
        return new JavaParser(parserConfiguration).parse(code).getResult().get();
    }

    /**
     * Tests for 6.3.1.1. Conditional-And Operator &&
     * https://docs.oracle.com/javase/specs/jls/se22/html/jls-6.html#jls-6.3.1.1
     *
     * The following rules apply to a conditional-and expression a && b
     * - A pattern variable introduced by a when true is definitely matched at b.
     * - A pattern variable is introduced by a && b when true iff either
     *     (i) it is introduced by a when true or
     *     (ii) it is introduced by b when true.
     */
    @Nested
    class ConditionalAnd {

        @Test
        public void conditionalAnd1() {
            CompilationUnit cu = parse("public class Test {\n"
                    + "    public void foo(Object o) {\n"
                    + "        if (o instanceof String value && value.length() > 5) { }\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertEquals("java.lang.String", name.resolve().getType().describe());
        }

        @Test
        public void conditionalAnd1Negated() {
            CompilationUnit cu = parse("public class Test {\n"
                    + "    public void foo(Object o) {\n"
                    + "        if (!(o instanceof String value) && value.length() > 5) { }\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertThrows(UnsolvedSymbolException.class, () -> name.resolve());
        }

        @Test
        public void conditionalAnd2_1() {
            CompilationUnit cu = parse("public class Test {\n"
                    + "    public void foo(Object o, boolean b) {\n"
                    + "        if (o instanceof String value && b) {\n"
                    + "            System.out.println(value);\n"
                    + "        }\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertEquals("java.lang.String", name.resolve().getType().describe());
        }

        @Test
        public void conditionalAnd2_2() {
            CompilationUnit cu = parse("public class Test {\n"
                    + "    public void foo(Object o, boolean b) {\n"
                    + "        if (b && o instanceof String value) {\n"
                    + "            System.out.println(value);\n"
                    + "        }\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertEquals("java.lang.String", name.resolve().getType().describe());
        }

        @Test
        public void conditionalAnd2_3() {
            CompilationUnit cu = parse("public class Test {\n"
                    + "    public void foo(Object o, Object p) {\n"
                    + "        if (o instanceof String value1 && p instanceof Integer value2) {\n"
                    + "            System.out.println(value1 + value2);\n"
                    + "        }\n"
                    + "    }\n"
                    + "}");

            NameExpr name1 = Navigator.findNameExpression(cu, "value1").get();
            assertEquals("java.lang.String", name1.resolve().getType().describe());
            NameExpr name2 = Navigator.findNameExpression(cu, "value2").get();
            assertEquals("java.lang.Integer", name2.resolve().getType().describe());
        }

        @Test
        public void conditionalAnd2_1Negated() {
            CompilationUnit cu = parse("public class Test {\n"
                    + "    public void foo(Object o, boolean b) {\n"
                    + "        if (!(o instanceof String value) && b) {\n"
                    + "            System.out.println(value);\n"
                    + "        }\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertThrows(UnsolvedSymbolException.class, () -> name.resolve());
        }

        @Test
        public void conditionalAnd2_2Negated() {
            CompilationUnit cu = parse("public class Test {\n"
                    + "    public void foo(Object o, boolean b) {\n"
                    + "        if (b && !(o instanceof String value)) {\n"
                    + "            System.out.println(value);\n"
                    + "        }\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertThrows(UnsolvedSymbolException.class, () -> name.resolve());
        }

        @Test
        public void conditionalAnd2_3Negated() {
            CompilationUnit cu = parse("public class Test {\n"
                    + "    public void foo(Object o, Object p) {\n"
                    + "        if (!(o instanceof String value1) && !(p instanceof Integer value2)) {\n"
                    + "            System.out.println(value1 + value2);\n"
                    + "        }\n"
                    + "    }\n"
                    + "}");

            NameExpr name1 = Navigator.findNameExpression(cu, "value1").get();
            assertThrows(UnsolvedSymbolException.class, () -> name1.resolve());
            NameExpr name2 = Navigator.findNameExpression(cu, "value2").get();
            assertThrows(UnsolvedSymbolException.class, () -> name2.resolve());
        }

        @Test
        public void conditionalAnd3() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o, boolean a, boolean b, boolean c, boolean d, boolean e) {\n"
                    + "        if (((a && ((o instanceof String value && b) && c)) && (d && (value.length() > 5 && e)))) {\n"
                    + "        }\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertEquals("java.lang.String", name.resolve().getType().describe());
        }

        @Test
        @Disabled("Until bug mentioned in https://github.com/javaparser/javaparser/issues/4344 is fixed")
        public void conditionalAnd4() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o) {\n"
                    + "        if (o instanceof Boolean value && value) { }\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertEquals("java.lang.Boolean", name.resolve().getType().describe());
        }
    }

    /**
     * Tests for 6.3.1.2. Conditional-Or Operator ||
     * https://docs.oracle.com/javase/specs/jls/se22/html/jls-6.html#jls-6.3.1.2
     *
     * The following rules apply to a conditional-or expression a || b
     * - A pattern variable introduced by a when false is definitely matched at b.
     * - A pattern variable is introduced by a || b when false iff either
     *     (i) it is introduced by a when false or
     *     (ii) it is introduced by b when false.
     */
    @Nested
    class ConditionalOr {
        @Test
        public void conditionalOr1() {
            CompilationUnit cu = parse("public class Test {\n"
                    + "    public void foo(Object o) {\n"
                    + "        if (!(o instanceof String value) || value.length() > 5) { }\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertEquals("java.lang.String", name.resolve().getType().describe());
        }

        @Test
        public void conditionalOr1Negated() {
            CompilationUnit cu = parse("public class Test {\n"
                    + "    public void foo(Object o) {\n"
                    + "        if (o instanceof String value || value.length() > 5) { }\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertThrows(UnsolvedSymbolException.class, () -> name.resolve());
        }

        @Test
        public void conditionalOr2_1() {
            CompilationUnit cu = parse("public class Test {\n"
                    + "    public void foo(Object o, boolean b) {\n"
                    + "        if (!(!(o instanceof String value) || b)) {\n"
                    + "            System.out.println(value);\n"
                    + "        }\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertEquals("java.lang.String", name.resolve().getType().describe());
        }

        @Test
        public void conditionalOr2_2() {
            CompilationUnit cu = parse("public class Test {\n"
                    + "    public void foo(Object o, boolean b) {\n"
                    + "        if (!(b || !(o instanceof String value))) {\n"
                    + "            System.out.println(value);\n"
                    + "        }\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertEquals("java.lang.String", name.resolve().getType().describe());
        }

        @Test
        public void conditionalOr2_1Negated() {
            CompilationUnit cu = parse("public class Test {\n"
                    + "    public void foo(Object o, boolean b) {\n"
                    + "        if (!(o instanceof String value || b)) {\n"
                    + "            System.out.println(value);\n"
                    + "        }\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertThrows(UnsolvedSymbolException.class, () -> name.resolve());
        }

        @Test
        public void conditionalOr2_2Negated() {
            CompilationUnit cu = parse("public class Test {\n"
                    + "    public void foo(Object o, boolean b) {\n"
                    + "        if (!(b || o instanceof String value)) {\n"
                    + "            System.out.println(value);\n"
                    + "        }\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertThrows(UnsolvedSymbolException.class, () -> name.resolve());
        }

        @Test
        public void conditionalOr3() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o, boolean a, boolean b, boolean c, boolean d, boolean e) {\n"
                    + "        if (((a || ((!(o instanceof String value) || b) || c)) || (d || (value.length() > 5 || e)))) {\n"
                    + "        }\n"
                    + "    }\n"
                    + "}\n");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertEquals("java.lang.String", name.resolve().getType().describe());
        }
    }

    /**
     * Tests for 6.3.1.3. Conditional-Or Operator ||
     * https://docs.oracle.com/javase/specs/jls/se22/html/jls-6.html#jls-6.3.1.3
     *
     * The following rules apply to a logical complement expression !a
     * - A pattern variable is introduced by !a when true iff it is introduced by a when false.
     * - A pattern variable is introduced by !a when false iff it is introduced by a when true.
     */
    @Nested
    class LogicalComplementOperator {
        @Test
        public void logicalComplementOperator1() {
            CompilationUnit cu = parse("public class Test {\n"
                    + "    public void foo(Object o) {\n"
                    + "        if (!(o instanceof String value)) {\n"
                    + "            System.out.println(value);\n"
                    + "        }\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertThrows(UnsolvedSymbolException.class, () -> name.resolve());
        }

        @Test
        public void logicalComplementOperator2() {
            CompilationUnit cu = parse("public class Test {\n"
                    + "    public void foo(Object o) {\n"
                    + "        if (!(!(o instanceof String value))) {\n"
                    + "            System.out.println(value);\n"
                    + "        }\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertEquals("java.lang.String", name.resolve().getType().describe());
        }
    }

    /**
     * Tests for 6.3.1.4. Conditional-Or Operator ||
     * https://docs.oracle.com/javase/specs/jls/se22/html/jls-6.html#jls-6.3.1.4
     *
     * The following rules apply to a conditional expression a ? b : c
     * - A pattern variable introduced by a when true is definitely matched at b.
     * - A pattern variable introduced by a when false is definitely matched at c.
     */
    @Nested
    class ConditionalOperator {

        @Test
        public void conditionalOperator1() {
            CompilationUnit cu = parse("public class Test {\n"
                    + "    public void foo(Object o) {\n"
                    + "      boolean b = o instanceof String value ? value.length() > 0 : false;\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertEquals("java.lang.String", name.resolve().getType().describe());
        }

        @Test
        public void conditionalOperator1Negated() {
            CompilationUnit cu = parse("public class Test {\n"
                    + "    public void foo(Object o) {\n"
                    + "      boolean b = o instanceof String value ? false : value.length() > 5;\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertThrows(UnsolvedSymbolException.class, () -> name.resolve());
        }

        @Test
        public void conditionalOperator2() {
            CompilationUnit cu = parse("public class Test {\n"
                    + "    public void foo(Object o) {\n"
                    + "      boolean b = !(o instanceof String value) ? false : value.length() > 5;\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertEquals("java.lang.String", name.resolve().getType().describe());
        }

        @Test
        public void conditionalOperator2Negated() {
            CompilationUnit cu = parse("public class Test {\n"
                    + "    public void foo(Object o) {\n"
                    + "      boolean b = !(o instanceof String value) ? value.length() > 0 : false;\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertThrows(UnsolvedSymbolException.class, () -> name.resolve());
        }
    }

    /**
     * Tests for 6.3.1.5. Pattern Match Operator instanceof
     * https://docs.oracle.com/javase/specs/jls/se22/html/jls-6.html#jls-6.3.1.5
     *
     * The following rule applies to an instanceof expression with a pattern operand, a instanceof p
     * - A pattern variable is introduced by a instanceof p when true iff the pattern p contains a declaration
     *   of the pattern variable
     */
    @Nested
    class PatternMatchOperator {
        @Test
        public void patternMatchOperator() {
            CompilationUnit cu = parse("public class Test {\n"
                    + "    public void foo(Object o) {\n"
                    + "        if (o instanceof String value) {\n"
                    + "            System.out.println(value);\n"
                    + "        }\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertEquals("java.lang.String", name.resolve().getType().describe());
        }
    }

    /**
     * Tests for 6.3.1.6. switch Expressions
     * https://docs.oracle.com/javase/specs/jls/se22/html/jls-6.html#jls-6.3.1.6
     *
     * The following rule applies to a switch expression with a switch block consisting of switch rules
     * - A pattern variable introduced by a switch label is definitely matched in the associated switch rule expression,
     * switch rule block, or switch rule throw statement.
     *
     * The following rules apply to a switch expression with a switch block consisting of switch labeled statement
     * groups
     * - A pattern variable introduced by a switch label is definitely matched in all the statements of the associated
     *   switch labeled statement group.
     * - A pattern variable introduced by a statement S contained in a switch labeled statement group is definitely
     *   matched at all the statements following S, if any, in the switch labeled statement group.
     */
    @Nested
    class SwitchExpressions {
        @Test
        public void switchExpressions1() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public String test(Object o) {\n"
                    + "        return switch (o) {\n"
                    + "            case String value -> value + \";\";\n"
                    + "            default -> \"\";\n"
                    + "        };\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertEquals("java.lang.String", name.resolve().getType().describe());
        }

        @Test
        public void switchExpressions1Negated() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public String test(Object o) {\n"
                    + "        return switch (o) {\n"
                    + "            case String value -> \";\";\n"
                    + "            default -> value + \"\";\n"
                    + "        };\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertThrows(UnsolvedSymbolException.class, () -> name.resolve());
        }

        @Test
        public void switchExpressions2() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o) {\n"
                    + "        switch (o) {\n"
                    + "            case String value -> {\n"
                    + "                String s = value;\n"
                    + "            }\n"
                    + "            default -> {}\n"
                    + "        }\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertEquals("java.lang.String", name.resolve().getType().describe());
        }

        @Test
        public void switchExpressions2Negated() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o) {\n"
                    + "        switch (o) {\n"
                    + "            case String value -> {\n"
                    + "            }\n"
                    + "            default -> {\n"
                    + "                String s = value;\n"
                    + "            }\n"
                    + "        }\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertThrows(UnsolvedSymbolException.class, () -> name.resolve());
        }

        @Test
        public void switchExpressions3() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o) {\n"
                    + "        switch (o) {\n"
                    + "            case String value -> throw new RuntimeException(value);\n"
                    + "            default -> {}\n"
                    + "        }\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertEquals("java.lang.String", name.resolve().getType().describe());
        }

        @Test
        public void switchExpressions3Negated() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o) {\n"
                    + "        switch (o) {\n"
                    + "            case String value -> {}\n"
                    + "            default -> throw new RuntimeException(value);\n"
                    + "        }\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertThrows(UnsolvedSymbolException.class, () -> name.resolve());
        }

        @Test
        public void switchExpressions4() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o) {\n"
                    + "        switch (o) {\n"
                    + "            case String value:\n"
                    + "                System.out.println(value);\n"
                    + "            default:\n"
                    + "        }\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertEquals("java.lang.String", name.resolve().getType().describe());
        }

        @Test
        public void switchExpressions4Negated() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o) {\n"
                    + "        switch (o) {\n"
                    + "            case String value:\n"
                    + "            default:\n"
                    + "                System.out.println(value);\n"
                    + "        }\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertThrows(UnsolvedSymbolException.class, () -> name.resolve());
        }

        @Test
        public void switchExpressions5() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o) {\n"
                    + "        switch (o) {\n"
                    + "            case Integer value:\n"
                    + "                System.out.println(value);\n"
                    + "            case String value:\n"
                    + "                System.out.println(value);\n"
                    + "            default:\n"
                    + "        }\n"
                    + "    }\n"
                    + "}");

            SwitchStmt switchStmt = cu.getClassByName("Test")
                    .get()
                    .getMethods()
                    .get(0)
                    .getBody()
                    .get()
                    .getStatements()
                    .get(0)
                    .asSwitchStmt();

            NameExpr firstValue = Navigator.findNameExpression(
                            switchStmt.getEntries().get(0), "value")
                    .get();
            assertEquals("java.lang.Integer", firstValue.resolve().getType().describe());
            NameExpr secondValue = Navigator.findNameExpression(
                            switchStmt.getEntries().get(1), "value")
                    .get();
            assertEquals("java.lang.String", secondValue.resolve().getType().describe());
        }

        @Test
        public void switchExpressions6() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o) {\n"
                    + "        switch (o) {\n"
                    + "            case Integer value:\n"
                    + "            case String otherValue:\n"
                    + "                System.out.println(value);\n"
                    + "            default:\n"
                    + "        }\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertThrows(UnsolvedSymbolException.class, () -> name.resolve());
        }
    }

    /**
     * Tests for 6.3.1.7. Parenthesized Expressions
     * https://docs.oracle.com/javase/specs/jls/se22/html/jls-6.html#jls-6.3.1.7
     *
     * The following rules apply to a parenthesized expression (a) (§15.8.5):
     * - A pattern variable is introduced by (a) when true iff it is introduced by a when true.
     * - A pattern variable is introduced by (a) when false iff it is introduced by a when false.
     */
    @Nested
    class ParenthesizedExpressions {
        @Test
        public void parenthesizedExpressions1() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o) {\n"
                    + "        if ((((((((o instanceof String value)))))))) {\n"
                    + "            System.out.println(value);\n"
                    + "        } else {\n"
                    + "        }\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertEquals("java.lang.String", name.resolve().getType().describe());
        }

        @Test
        public void parenthesizedExpressions1Negated() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o) {\n"
                    + "        if ((((((((o instanceof String value)))))))) {\n"
                    + "        } else {\n"
                    + "            System.out.println(value);\n"
                    + "        }\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertThrows(UnsolvedSymbolException.class, () -> name.resolve());
        }

        @Test
        public void parenthesizedExpressions2() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o) {\n"
                    + "        if (!(((((((o instanceof String value)))))))) {\n"
                    + "        } else {\n"
                    + "            System.out.println(value);\n"
                    + "        }\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertEquals("java.lang.String", name.resolve().getType().describe());
        }

        @Test
        public void parenthesizedExpressions2Negated() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o) {\n"
                    + "        if (!(((((((o instanceof String value)))))))) {\n"
                    + "            System.out.println(value);\n"
                    + "        } else {\n"
                    + "        }\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertThrows(UnsolvedSymbolException.class, () -> name.resolve());
        }
    }

    /**
     * Tests for 6.3.2.2. if Statements
     * https://docs.oracle.com/javase/specs/jls/se22/html/jls-6.html#jls-6.3.2.2
     *
     * The following rules apply to a statement if (e) S
     * - A pattern variable introduced by e when true is definitely matched at S.
     * - A pattern variable is introduced by if (e) S iff
     *   (i) it is introduced by e when false and
     *   (ii) S cannot complete normally.
     *
     * The following rules apply to a statement if (e) S else T
     * - A pattern variable introduced by e when true is definitely matched at S.
     * - A pattern variable introduced by e when false is definitely matched at T.
     * - A pattern variable is introduced by if (e) S else T iff either:
     *   - It is introduced by e when true, and S can complete normally, and T cannot complete normally; or
     *   - It is introduced by e when false, and S cannot complete normally, and T can complete normally.
     *
     */
    @Nested
    class IfStatements {
        @Test
        public void ifStatements1() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o) {\n"
                    + "        if (o instanceof String value) {\n"
                    + "            System.out.println(value);\n"
                    + "        }\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertEquals("java.lang.String", name.resolve().getType().describe());
        }

        @Test
        public void ifStatements1Negated1() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o) {\n"
                    + "        if (!(o instanceof String value)) {\n"
                    + "            System.out.println(value);\n"
                    + "        }\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertThrows(UnsolvedSymbolException.class, () -> name.resolve());
        }

        @Test
        public void ifStatements1Negated2() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o, boolean b) {\n"
                    + "        if (o instanceof String value || b) {\n"
                    + "            System.out.println(value);\n"
                    + "        }\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertThrows(UnsolvedSymbolException.class, () -> name.resolve());
        }

        @Test
        public void ifStatements2() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o) {\n"
                    + "        if (!(o instanceof String value)) {\n"
                    + "            return;\n"
                    + "        }\n"
                    + "        System.out.println(value);\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertEquals("java.lang.String", name.resolve().getType().describe());
        }

        @Test
        public void ifStatements2Negated1() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o) {\n"
                    + "        if (o instanceof String value) {\n"
                    + "            return;\n"
                    + "        }\n"
                    + "        System.out.println(value);\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertThrows(UnsolvedSymbolException.class, () -> name.resolve());
        }

        @Test
        public void ifStatements2Negated2() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o) {\n"
                    + "        if (!(o instanceof String value)) {\n"
                    + "        }\n"
                    + "        System.out.println(value);\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertThrows(UnsolvedSymbolException.class, () -> name.resolve());
        }

        @Test
        public void ifStatements3() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o) {\n"
                    + "        if (!(o instanceof String value)) {\n"
                    + "            throw new RuntimeException();\n"
                    + "        }\n"
                    + "        System.out.println(value);\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertEquals("java.lang.String", name.resolve().getType().describe());
        }

        @Test
        public void ifStatements4() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o) {\n"
                    + "        if (o instanceof String value) {\n"
                    + "            System.out.println(value);\n"
                    + "        } else {\n"
                    + "        }\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertEquals("java.lang.String", name.resolve().getType().describe());
        }

        @Test
        public void ifStatements4Negated() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o) {\n"
                    + "        if (o instanceof String value) {\n"
                    + "        } else {\n"
                    + "            System.out.println(value);\n"
                    + "        }\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertThrows(UnsolvedSymbolException.class, () -> name.resolve());
        }

        @Test
        public void ifStatements5() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o) {\n"
                    + "        if (!(o instanceof String value)) {\n"
                    + "        } else {\n"
                    + "            System.out.println(value);\n"
                    + "        }\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertEquals("java.lang.String", name.resolve().getType().describe());
        }

        @Test
        public void ifStatements5Negated() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o) {\n"
                    + "        if (!(o instanceof String value)) {\n"
                    + "            System.out.println(value);\n"
                    + "        } else {\n"
                    + "        }\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertThrows(UnsolvedSymbolException.class, () -> name.resolve());
        }

        @Test
        public void ifStatements6() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o) {\n"
                    + "        if (o instanceof String value) {\n"
                    + "        } else {\n"
                    + "            return;\n"
                    + "        }\n"
                    + "        System.out.println(value);\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertEquals("java.lang.String", name.resolve().getType().describe());
        }

        @Test
        public void ifStatements6Negated() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o) {\n"
                    + "        if (o instanceof String value) {\n"
                    + "        } else {\n"
                    + "        }\n"
                    + "        System.out.println(value);\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertThrows(UnsolvedSymbolException.class, () -> name.resolve());
        }

        @Test
        public void ifStatements7() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o) {\n"
                    + "        if (!(o instanceof String value)) {\n"
                    + "            return;\n"
                    + "        } else {\n"
                    + "        }\n"
                    + "        System.out.println(value);\n"
                    + "    }\n"
                    + "}");
            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertEquals("java.lang.String", name.resolve().getType().describe());
        }

        @Test
        public void ifStatements7Negated() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o) {\n"
                    + "        if (!(o instanceof String value)) {\n"
                    + "        } else {\n"
                    + "            return;\n"
                    + "        }\n"
                    + "        System.out.println(value);\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertThrows(UnsolvedSymbolException.class, () -> name.resolve());
        }
    }

    /**
     * Tests for 6.3.2.3. while Statements
     * https://docs.oracle.com/javase/specs/jls/se22/html/jls-6.html#jls-6.3.2.3
     *
     *  The following rules apply to a statement while (e) S
     *  - A pattern variable introduced by e when true is definitely matched at S.
     *  - A pattern variable is introduced by while (e) S iff
     *    (i) it is introduced by e when false and
     *    (ii) S does not contain a reachable break statement for which the while statement is the break target
     */
    @Nested
    class WhileStatements {
        @Test
        public void whileStatements1() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o) {\n"
                    + "        while (o instanceof String value) {\n"
                    + "            System.out.println(value);\n"
                    + "        }\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertEquals("java.lang.String", name.resolve().getType().describe());
        }

        @Test
        public void whileStatements1Negated1() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o) {\n"
                    + "        while (!(o instanceof String value)) {\n"
                    + "            System.out.println(value);\n"
                    + "        }\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertThrows(UnsolvedSymbolException.class, () -> name.resolve());
        }

        @Test
        public void whileStatements1Negated2() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o, boolean b) {\n"
                    + "        while (o instanceof String value || b) {\n"
                    + "            System.out.println(value);\n"
                    + "        }\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertThrows(UnsolvedSymbolException.class, () -> name.resolve());
        }

        @Test
        public void whileStatements2() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o) {\n"
                    + "        while (!(o instanceof String value)) {\n"
                    + "        }\n"
                    + "        System.out.println(value);\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertEquals("java.lang.String", name.resolve().getType().describe());
        }

        @Test
        public void whileStatements2Negated1() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o) {\n"
                    + "        while (!(o instanceof String value)) {\n"
                    + "            break;\n"
                    + "        }\n"
                    + "        System.out.println(value);\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertThrows(UnsolvedSymbolException.class, () -> name.resolve());
        }

        @Test
        public void whileStatements3() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o) {\n"
                    + "        first:\n"
                    + "        while (true) {\n"
                    + "            while (!(o instanceof String value)) {\n"
                    + "                break first;\n"
                    + "            }\n"
                    + "            System.out.println(value);\n"
                    + "        }\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertEquals("java.lang.String", name.resolve().getType().describe());
        }

        @Test
        public void whileStatements4() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o) {\n"
                    + "        first:\n"
                    + "        while (!(o instanceof String value)) {\n"
                    + "            break first;\n"
                    + "        }\n"
                    + "        System.out.println(value);\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertThrows(UnsolvedSymbolException.class, () -> name.resolve());
        }

        @Test
        public void whileStatements5() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o) {\n"
                    + "        while (o instanceof String value)\n"
                    + "            System.out.println(value);\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertEquals("java.lang.String", name.resolve().getType().describe());
        }
    }

    /**
     * Tests for 6.3.2.4. do Statements
     * https://docs.oracle.com/javase/specs/jls/se22/html/jls-6.html#jls-6.3.2.4
     *
     * The following rule applies to a statement do S while (e)
     * - A pattern variable is introduced by do S while (e) iff
     *   (i) it is introduced by e when false and
     *   (ii) S does not contain a reachable break statement for which the do statement is the break target
     */
    @Nested
    class DoStatements {
        @Test
        public void doStatements1() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o) {\n"
                    + "        do {\n"
                    + "        } while (!(o instanceof String value));\n"
                    + "        System.out.println(value);\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertEquals("java.lang.String", name.resolve().getType().describe());
        }

        @Test
        public void doStatements1Negated1() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o) {\n"
                    + "        do {\n"
                    + "            break;"
                    + "        } while (!(o instanceof String value));\n"
                    + "        System.out.println(value);\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertThrows(UnsolvedSymbolException.class, () -> name.resolve());
        }
    }

    /**
     * Tests for 6.3.2.5. for Statements
     * https://docs.oracle.com/javase/specs/jls/se22/html/jls-6.html#jls-6.3.2.5
     *
     *  The following rules apply to a basic for statement
     *  - A pattern variable introduced by the condition expression when true is definitely matched at both the
     *    incrementation part and the contained statement.
     *  - A pattern variable is introduced by a basic for statement iff
     *    (i) it is introduced by the condition expression when false and
     *    (ii) the contained statement, S, does not contain a reachable break for which the basic for statement is the
     *         break target
     *
     * An enhanced for statement is defined by translation to a basic for statement, so no special rules need to be
     * provided for it.
     */
    @Nested
    class ForStatements {
        @Test
        public void forStatements1() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o) {\n"
                    + "        for (int i = 0; o instanceof String value; i += value.length()) { }\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertEquals("java.lang.String", name.resolve().getType().describe());
        }

        @Test
        public void forStatements1Negated() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o) {\n"
                    + "        for (int i = 0; o instanceof String value || i < 3; i += value.length()) { }\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertThrows(UnsolvedSymbolException.class, () -> name.resolve());
        }

        @Test
        public void forStatements2() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o) {\n"
                    + "        for (; o instanceof String value; ) {\n"
                    + "            System.out.println(value);\n"
                    + "        }\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertEquals("java.lang.String", name.resolve().getType().describe());
        }

        @Test
        public void forStatements2Negated() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o) {\n"
                    + "        for (; !(o instanceof String value); ) {\n"
                    + "            System.out.println(value);\n"
                    + "        }\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertThrows(UnsolvedSymbolException.class, () -> name.resolve());
        }

        @Test
        public void forStatements3() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o) {\n"
                    + "        for (; !(o instanceof String value); ) {\n"
                    + "        }\n"
                    + "        System.out.println(value);\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertEquals("java.lang.String", name.resolve().getType().describe());
        }

        @Test
        public void forStatements3Negated() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o) {\n"
                    + "        for (; !(o instanceof String value); ) {\n"
                    + "            break;\n"
                    + "        }\n"
                    + "        System.out.println(value);\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertThrows(UnsolvedSymbolException.class, () -> name.resolve());
        }

        @Test
        public void forStatements4() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o) {\n"
                    + "        for (int i = 0; o instanceof String value; value.length()) { }\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertEquals("java.lang.String", name.resolve().getType().describe());
        }

        @Test
        public void forStatements4Negated() {
            CompilationUnit cu = parse("class Test {\n"
                    + "    public void test(Object o) {\n"
                    + "        for (int i = 0; !(o instanceof String value); value.length()) { }\n"
                    + "    }\n"
                    + "}");

            NameExpr name = Navigator.findNameExpression(cu, "value").get();
            assertThrows(UnsolvedSymbolException.class, () -> name.resolve());
        }
    }
}
