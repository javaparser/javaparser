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

package com.github.javaparser.ast.expr;

import static com.github.javaparser.ast.stmt.SwitchEntry.Type.*;
import static com.github.javaparser.utils.TestParser.*;
import static org.junit.jupiter.api.Assertions.*;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.Range;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.stmt.SwitchEntry;
import com.github.javaparser.ast.stmt.SwitchStmt;
import com.github.javaparser.resolution.Navigator;
import org.junit.jupiter.api.Test;

class SwitchExprTest {
    @Test
    void jep325Example2() {
        NodeList<Expression> entry2labels = parseStatement(
                        """
                        int numLetters = switch (day) {
                            case MONDAY, FRIDAY, SUNDAY -> 6;
                            case TUESDAY                -> 7;
                            case THURSDAY, SATURDAY     -> 8;
                            case WEDNESDAY              -> 9;
                        };\
                        """)
                .findAll(SwitchEntry.class)
                .get(0)
                .getLabels();

        assertEquals(3, entry2labels.size());
        assertEquals("MONDAY", entry2labels.get(0).toString());
        assertEquals("FRIDAY", entry2labels.get(1).toString());
        assertEquals("SUNDAY", entry2labels.get(2).toString());
    }

    @Test
    void funkyExpressions() {
        parseStatement("""
                int numLetters = switch (day) {
                    case 1+1, 2+2 -> 6;
                    case "Henk"-> 7;
                    case ((3)+3)+3 -> 8;
                };\
                """);
    }

    @Test
    void jep325Example3() {
        parseBodyDeclaration("""
                static void howMany(int k) {
                    switch (k) {
                        case 1 -> System.out.println("one");
                        case 2 -> System.out.println("two");
                        case 3 -> System.out.println("many");
                    }
                }\
                """);
    }

    @Test
    void aThrowStatement() {
        SwitchExpr switchExpr = parseExpression("""
                        switch (k) {
                                case 1 -> throw new Exception("one");
                                case 2 -> 42;
                            }\
                        """)
                .findFirst(SwitchExpr.class)
                .get();

        assertEquals(THROWS_STATEMENT, switchExpr.getEntry(0).getType());
        assertEquals(EXPRESSION, switchExpr.getEntry(1).getType());
    }

    @Test
    void jep325Example4() {
        SwitchExpr switchExpr = parseStatement("""
                        T result = switch (arg) {
                            case L1 -> e1;
                            case L2 -> e2;
                            default -> e3;
                        };\
                        """)
                .findFirst(SwitchExpr.class)
                .get();

        assertEquals(EXPRESSION, switchExpr.getEntry(0).getType());
    }

    @Test
    void jep325Example5() {
        SwitchExpr switchExpr = parseStatement("""
                        int j = switch (day) {
                            case MONDAY  -> 0;
                            case TUESDAY -> 1;
                            default      -> {
                                int k = day.toString().length();
                                int result = f(k);
                                yield result;
                            }
                        };\
                        """)
                .findFirst(SwitchExpr.class)
                .get();

        assertEquals(BLOCK, switchExpr.getEntry(2).getType());
        assertEquals(
                BlockStmt.class, switchExpr.getEntry(2).getStatements().get(0).getClass());
    }

    @Test
    void jep325Example6() {
        parseStatement("""
                int result = switch (s) {
                    case "Foo":\s
                        yield 1;
                    case "Bar":
                        yield 2;
                    default:
                        System.out.println("Neither Foo nor Bar, hmmm...");
                        yield 0;
                };\
                """);
    }

    @Test
    void yieldMethodCall() {
        parseStatement("""
                int randomNumber = switch (5) {
                    default -> {
                        yield a.randomNumberGenerator();
                    }
                    case 1 -> {
                        yield method();
                    }
                    case 2 -> {
                        yield method(args);
                    }
                    case 3 -> {
                        yield this.method();
                    }
                    case 4 -> {
                        yield Clazz.this.method(args);
                    }
                };\
                """);
    }

    @Test
    void yieldExpression1() {
        parseStatement("""
                int randomNumber = switch (5) {
                    default -> {
                        yield 1 * 1;
                    }
                    case 1 -> {
                        yield (5 + 5);
                    }
                    case 2 -> {
                        yield (5 + 5) * 3;
                    }
                };\
                """);
    }

    @Test
    void yieldExpression2() {
        parseStatement("""
                boolean b = switch (5) {
                    case 3 -> {
                        yield true || false;
                    }
                    default -> {
                        yield !true;
                    }
                };\
                """);
    }

    @Test
    void yieldAssignment() {
        parseStatement("""
                int randomNumber = switch (5) {
                    default -> {
                        int x;
                        yield (x = 5);
                    }
                    case 'a' -> {
                        int x;
                        yield x = 3;
                    }
                };\
                """);
    }

    @Test
    void yieldConditional() {
        parseStatement("""
                int randomNumber = switch (5) {
                    default -> {
                        yield x ? 1 : 2;
                    }
                    case 1 -> {
                        yield (x ? 1 : 2);
                    }
                    case 2 -> {
                        yield x < 0 ? 0 : x > y ? y : x;
                    }
                };\
                """);
    }

    @Test
    void yieldYield() {
        parseStatement("""
                yield = switch (yield) {
                    default -> {
                        yield yield;
                    }
                    case yield -> {
                        yield Clazz.yield();
                    }
                    case enumValue2 -> {
                        yield yield = yield;
                    }
                    case enumValue3 -> {
                        yield yield == yield ? yield : yield;
                    }
                };\
                """);
    }

    @Test
    void switchPattern() {
        SwitchStmt stmt = parseStatement("switch (value) {\n" + "    case Box b -> System.out.println(b);\n" + "}")
                .asSwitchStmt();

        assertEquals(1, stmt.getEntries().size());

        SwitchEntry entry = stmt.getEntry(0);
        assertFalse(entry.getGuard().isPresent());

        assertEquals(1, entry.getLabels().size());

        TypePatternExpr label = entry.getLabels().get(0).asTypePatternExpr();

        assertEquals("b", label.getNameAsString());
        assertEquals("Box", label.getTypeAsString());
    }

    @Test
    void switchPatternWithGuard() {
        SwitchExpr expr = parseExpression(
                        """
                        switch (value) {
                            case Box b when b.nonEmpty() -> b.get() + 12;
                        }\
                        """)
                .asSwitchExpr();

        assertEquals(1, expr.getEntries().size());

        SwitchEntry entry = expr.getEntry(0);
        assertTrue(entry.getGuard().isPresent());

        Expression guard = entry.getGuard().get();
        assertInstanceOf(MethodCallExpr.class, guard);

        assertEquals(1, entry.getLabels().size());
        TypePatternExpr label = entry.getLabels().get(0).asTypePatternExpr();

        assertEquals("b", label.getNameAsString());
        assertEquals("Box", label.getTypeAsString());

        assertEquals("b.get() + 12;", entry.getStatements().get(0).toString());
    }

    @Test
    void testRemoveGuard() {
        SwitchExpr expr = parseExpression("switch (value) {\n" + "    case Box b when b.nonEmpty() -> {}\n" + "}")
                .asSwitchExpr();

        SwitchEntry entry = expr.getEntry(0);

        assertTrue(entry.getGuard().isPresent());

        entry.removeGuard();

        assertFalse(entry.getGuard().isPresent());

        assertFalse(Navigator.findNameExpression(entry, "b").isPresent());
    }

    @Test
    void testRemoveWithGuard() {
        SwitchExpr expr = parseExpression("switch (value) {\n" + "    case Box b when b.nonEmpty() -> {}\n" + "}")
                .asSwitchExpr();

        SwitchEntry entry = expr.getEntry(0);

        assertTrue(entry.getGuard().isPresent());

        entry.remove(entry.getGuard().get());

        assertFalse(entry.getGuard().isPresent());

        assertFalse(Navigator.findNameExpression(entry, "b").isPresent());
    }

    @Test
    void testRecordPattern() {
        SwitchExpr expr = parseExpression(
                        """
                        switch (value) {
                            case TwoBox (String s, Box(Integer i)) -> {}
                        }\
                        """)
                .asSwitchExpr();

        SwitchEntry entry = expr.getEntry(0);

        assertTrue(entry.getLabels().get(0).isRecordPatternExpr());

        RecordPatternExpr recordPattern = entry.getLabels().get(0).asRecordPatternExpr();

        assertEquals("TwoBox", recordPattern.getTypeAsString());

        assertEquals(2, recordPattern.getPatternList().size());

        assertTrue(recordPattern.getPatternList().get(0).isTypePatternExpr());
        TypePatternExpr stringPattern = recordPattern.getPatternList().get(0).asTypePatternExpr();
        assertEquals("String", stringPattern.getTypeAsString());
        assertEquals("s", stringPattern.getNameAsString());

        assertTrue(recordPattern.getPatternList().get(1).isRecordPatternExpr());
        RecordPatternExpr boxPattern = recordPattern.getPatternList().get(1).asRecordPatternExpr();
        assertEquals("Box", boxPattern.getTypeAsString());

        assertEquals(1, boxPattern.getPatternList().size());

        assertTrue(boxPattern.getPatternList().get(0).isTypePatternExpr());
        TypePatternExpr integerPattern = boxPattern.getPatternList().get(0).asTypePatternExpr();
        assertEquals("Integer", integerPattern.getTypeAsString());
        assertEquals("i", integerPattern.getNameAsString());
    }

    /**
     * Credit to @Kimmmey in https://github.com/javaparser/javaparser/issues/4440 for the
     * example code.
     */
    @Test
    void testSwitchExprUnaryMinus() {
        Statement stmt =
                parseStatement("int i = switch (x) {\n" + "    case 0 -> 0;\n" + "    default -> -1;\n" + "};");

        VariableDeclarator declarator =
                (VariableDeclarator) stmt.getChildNodes().get(0).getChildNodes().get(0);
        SwitchExpr switchExpr = declarator.getInitializer().get().asSwitchExpr();

        assertEquals("0", switchExpr.getEntry(0).getLabels().get(0).toString());
        assertEquals("0;", switchExpr.getEntry(0).getStatements().get(0).toString());

        assertTrue(switchExpr.getEntry(1).getLabels().isEmpty());
        assertTrue(switchExpr.getEntry(1).isDefault());
        assertEquals("-1;", switchExpr.getEntry(1).getStatements().get(0).toString());
    }

    /**
     * Credit to @Kimmmey in https://github.com/javaparser/javaparser/issues/4440 for the
     * example code.
     */
    @Test
    void testSwitchExprUnaryNot() {
        Statement stmt = parseStatement(
                """
                boolean b = switch (x) {
                    case 0 -> true;
                    default -> !false;
                };\
                """);

        VariableDeclarator declarator =
                (VariableDeclarator) stmt.getChildNodes().get(0).getChildNodes().get(0);
        SwitchExpr switchExpr = declarator.getInitializer().get().asSwitchExpr();

        assertEquals("0", switchExpr.getEntry(0).getLabels().get(0).toString());
        assertEquals("true;", switchExpr.getEntry(0).getStatements().get(0).toString());

        assertTrue(switchExpr.getEntry(1).getLabels().isEmpty());
        assertTrue(switchExpr.getEntry(1).isDefault());
        assertEquals("!false;", switchExpr.getEntry(1).getStatements().get(0).toString());
    }

    /**
     * Credit to @Kimmmey in https://github.com/javaparser/javaparser/issues/4440 for the
     * example code.
     */
    @Test
    void testSwitchExprWithBinaryExpr() {
        Statement stmt = parseStatement("""
                int i = switch (x) {
                    case 1 -> 1;
                    case 2, 3 -> 1 + 2;
                    default -> 1;
                };\
                """);

        VariableDeclarator declarator =
                (VariableDeclarator) stmt.getChildNodes().get(0).getChildNodes().get(0);
        SwitchExpr switchExpr = declarator.getInitializer().get().asSwitchExpr();

        assertEquals("1", switchExpr.getEntry(0).getLabels().get(0).toString());
        assertEquals("1;", switchExpr.getEntry(0).getStatements().get(0).toString());

        assertEquals("2", switchExpr.getEntry(1).getLabels().get(0).toString());
        assertEquals("3", switchExpr.getEntry(1).getLabels().get(1).toString());
        assertEquals("1 + 2;", switchExpr.getEntry(1).getStatements().get(0).toString());

        assertTrue(switchExpr.getEntry(2).getLabels().isEmpty());
        assertTrue(switchExpr.getEntry(2).isDefault());
        assertEquals("1;", switchExpr.getEntry(2).getStatements().get(0).toString());
    }

    @Test
    void testSwitchExprWithAssignment() {
        Statement stmt = parseStatement("""
                {
                    int z;
                    int i = switch (x) {
                        case 1 -> z = 1;
                        default -> 1;
                    };
                }\
                """);

        VariableDeclarator declarator = (VariableDeclarator) stmt.getChildNodes()
                .get(1)
                .getChildNodes()
                .get(0)
                .getChildNodes()
                .get(0);
        SwitchExpr switchExpr = declarator.getInitializer().get().asSwitchExpr();

        assertEquals("1", switchExpr.getEntry(0).getLabels().get(0).toString());
        assertEquals("z = 1;", switchExpr.getEntry(0).getStatements().get(0).toString());

        assertTrue(switchExpr.getEntry(1).getLabels().isEmpty());
        assertTrue(switchExpr.getEntry(1).isDefault());
        assertEquals("1;", switchExpr.getEntry(1).getStatements().get(0).toString());
    }

    @Test
    void issue4455Test() {
        SwitchExpr switchExpr = parseExpression(
                        """
                        switch (column) {
                            case CustomDeployTableModel.ARTIFACT_NAME -> {}
                        }\
                        """)
                .asSwitchExpr();

        assertEquals(Node.Parsedness.PARSED, switchExpr.getParsed());

        SwitchEntry entry = switchExpr.getEntry(0);
        Expression switchLabel = entry.getLabels().get(0);

        assertEquals("CustomDeployTableModel.ARTIFACT_NAME", switchLabel.toString());
        assertTrue(switchLabel.isFieldAccessExpr());
        assertTrue(switchLabel.getRange().isPresent());

        Range switchLabelRange = switchLabel.getRange().get();
        assertEquals(2, switchLabelRange.begin.line);
        assertEquals(10, switchLabelRange.begin.column);
        assertEquals(2, switchLabelRange.end.line);
        assertEquals(45, switchLabelRange.end.column);
    }

    @Test
    void switchExprWithoutTokensStored() {
        ParserConfiguration config = new ParserConfiguration();
        config.setStoreTokens(false);
        config.setLanguageLevel(ParserConfiguration.LanguageLevel.BLEEDING_EDGE);
        JavaParser parser = new JavaParser(config);

        ParseResult<SwitchExpr> result =
                parser.parseExpression("switch (o) {\n" + "    case Foo f -> f.get();\n" + "}");

        assertTrue(result.isSuccessful());
        assertTrue(result.getProblems().isEmpty());

        SwitchEntry entry = result.getResult().get().getEntry(0);
        assertEquals("Foo f", entry.getLabels().get(0).toString());
        assertEquals("f.get();", entry.getStatements().get(0).toString());
    }

    @Test
    void testRecordPatternWithPrimitiveType() {
        SwitchExpr switchExpr =
                parseExpression("switch (foo) { case Foo(int x) -> sink(x); }").asSwitchExpr();

        assertEquals(Node.Parsedness.PARSED, switchExpr.getParsed());

        SwitchEntry entry = switchExpr.getEntry(0);
        Expression switchLabel = entry.getLabels().get(0);

        assertEquals("Foo(int x)", switchLabel.toString());
        assertTrue(switchLabel.isRecordPatternExpr());

        RecordPatternExpr recordPattern = switchLabel.asRecordPatternExpr();

        assertEquals("Foo", recordPattern.getType().toString());
        assertEquals(1, recordPattern.getPatternList().size());
        assertTrue(recordPattern.getPatternList().get(0).isTypePatternExpr());

        TypePatternExpr innerType = recordPattern.getPatternList().get(0).asTypePatternExpr();

        assertTrue(innerType.getType().isPrimitiveType());
    }

    @Test
    void switchWithMatchAllPattern() {
        SwitchStmt stmt = parseStatement("switch (value) {\n" + "    case Box(_) -> System.out.println(0);\n" + "}")
                .asSwitchStmt();

        assertEquals(1, stmt.getEntries().size());

        SwitchEntry entry = stmt.getEntry(0);
        assertFalse(entry.getGuard().isPresent());

        assertEquals(1, entry.getLabels().size());

        assertTrue(entry.getLabels().get(0).isRecordPatternExpr());

        RecordPatternExpr recordPattern = entry.getLabels().get(0).asRecordPatternExpr();
        assertEquals(1, recordPattern.getPatternList().size());

        assertTrue(recordPattern.getPatternList().get(0).isMatchAllPatternExpr());
    }

    @Test
    void switchWithUnnamedTypePattern() {
        SwitchStmt stmt = parseStatement("switch (value) {\n" + "    case Box _ -> System.out.println(0);\n" + "}")
                .asSwitchStmt();

        assertEquals(1, stmt.getEntries().size());

        SwitchEntry entry = stmt.getEntry(0);
        assertFalse(entry.getGuard().isPresent());

        assertEquals(1, entry.getLabels().size());

        assertTrue(entry.getLabels().get(0).isTypePatternExpr());

        TypePatternExpr typePattern = entry.getLabels().get(0).asTypePatternExpr();
        assertEquals("Box", typePattern.getTypeAsString());
        assertEquals("_", typePattern.getNameAsString());
    }
}
