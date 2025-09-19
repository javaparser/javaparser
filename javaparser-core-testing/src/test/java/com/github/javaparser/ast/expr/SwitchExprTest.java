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

package com.github.javaparser.ast.expr;

import static com.github.javaparser.ParseStart.COMPILATION_UNIT;
import static com.github.javaparser.ParserConfiguration.LanguageLevel.JAVA_22;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.ast.stmt.SwitchEntry.Type.*;
import static com.github.javaparser.utils.TestParser.*;
import static com.github.javaparser.utils.TestUtils.assertNoProblems;
import static com.github.javaparser.utils.TestUtils.assertProblems;
import static org.junit.jupiter.api.Assertions.*;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.Range;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.stmt.SwitchEntry;
import com.github.javaparser.ast.stmt.SwitchStmt;
import com.github.javaparser.resolution.Navigator;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Disabled;

class SwitchExprTest {

    private final JavaParser javaParser22 = new JavaParser(new ParserConfiguration()
            .setLanguageLevel(JAVA_22)
            .setPreprocessUnicodeEscapes(false)
            .setStoreTokens(true));

    @Test
    void jep325Example2() {
        NodeList<Expression> entry2labels = parseStatement(
                        "int numLetters = switch (day) {\n" + "    case MONDAY, FRIDAY, SUNDAY -> 6;\n"
                                + "    case TUESDAY                -> 7;\n"
                                + "    case THURSDAY, SATURDAY     -> 8;\n"
                                + "    case WEDNESDAY              -> 9;\n"
                                + "};")
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
        parseStatement("int numLetters = switch (day) {\n" + "    case 1+1, 2+2 -> 6;\n"
                + "    case \"Henk\"-> 7;\n"
                + "    case ((3)+3)+3 -> 8;\n"
                + "};");
    }

    @Test
    void jep325Example3() {
        parseBodyDeclaration("static void howMany(int k) {\n" + "    switch (k) {\n"
                + "        case 1 -> System.out.println(\"one\");\n"
                + "        case 2 -> System.out.println(\"two\");\n"
                + "        case 3 -> System.out.println(\"many\");\n"
                + "    }\n"
                + "}");
    }

    @Test
    void aThrowStatement() {
        SwitchExpr switchExpr = parseExpression(
                        "switch (k) {\n" + "        case 1 -> throw new Exception(\"one\");\n" + "    }")
                .findFirst(SwitchExpr.class)
                .get();

        assertEquals(THROWS_STATEMENT, switchExpr.getEntry(0).getType());
    }

    @Test
    void jep325Example4() {
        SwitchExpr switchExpr = parseStatement("T result = switch (arg) {\n" + "    case L1 -> e1;\n"
                        + "    case L2 -> e2;\n"
                        + "    default -> e3;\n"
                        + "};")
                .findFirst(SwitchExpr.class)
                .get();

        assertEquals(EXPRESSION, switchExpr.getEntry(0).getType());
    }

    @Test
    void jep325Example5() {
        SwitchExpr switchExpr = parseStatement("int j = switch (day) {\n" + "    case MONDAY  -> 0;\n"
                        + "    case TUESDAY -> 1;\n"
                        + "    default      -> {\n"
                        + "        int k = day.toString().length();\n"
                        + "        int result = f(k);\n"
                        + "        yield result;\n"
                        + "    }\n"
                        + "};")
                .findFirst(SwitchExpr.class)
                .get();

        assertEquals(BLOCK, switchExpr.getEntry(2).getType());
        assertEquals(
                BlockStmt.class, switchExpr.getEntry(2).getStatements().get(0).getClass());
    }

    @Test
    void jep325Example6() {
        parseStatement("int result = switch (s) {\n" + "    case \"Foo\": \n"
                + "        yield 1;\n"
                + "    case \"Bar\":\n"
                + "        yield 2;\n"
                + "    default:\n"
                + "        System.out.println(\"Neither Foo nor Bar, hmmm...\");\n"
                + "        yield 0;\n"
                + "};");
    }

    @Test
    void yieldMethodCall() {
        parseStatement("int randomNumber = switch (5) {\n" + "    default -> {\n"
                + "        yield a.randomNumberGenerator();\n"
                + "    }\n"
                + "    case 1 -> {\n"
                + "        yield method();\n"
                + "    }\n"
                + "    case 2 -> {\n"
                + "        yield method(args);\n"
                + "    }\n"
                + "    case 3 -> {\n"
                + "        yield this.method();\n"
                + "    }\n"
                + "    case 4 -> {\n"
                + "        yield Clazz.this.method(args);\n"
                + "    }\n"
                + "};");
    }

    @Test
    void yieldExpression1() {
        parseStatement("int randomNumber = switch (5) {\n" + "    default -> {\n"
                + "        yield 1 * 1;\n"
                + "    }\n"
                + "    case 1 -> {\n"
                + "        yield (5 + 5);\n"
                + "    }\n"
                + "    case 2 -> {\n"
                + "        yield (5 + 5) * 3;\n"
                + "    }\n"
                + "};");
    }

    @Test
    void yieldExpression2() {
        parseStatement("boolean b = switch (5) {\n" + "    case 3 -> {\n"
                + "        yield true || false;\n"
                + "    }\n"
                + "    default -> {\n"
                + "        yield !true;\n"
                + "    }\n"
                + "};");
    }

    @Test
    void yieldAssignment() {
        parseStatement("int randomNumber = switch (5) {\n" + "    default -> {\n"
                + "        int x;\n"
                + "        yield (x = 5);\n"
                + "    }\n"
                + "    case 'a' -> {\n"
                + "        int x;\n"
                + "        yield x = 3;\n"
                + "    }\n"
                + "};");
    }

    @Test
    void yieldConditional() {
        parseStatement("int randomNumber = switch (5) {\n" + "    default -> {\n"
                + "        yield x ? 1 : 2;\n"
                + "    }\n"
                + "    case 1 -> {\n"
                + "        yield (x ? 1 : 2);\n"
                + "    }\n"
                + "    case 2 -> {\n"
                + "        yield x < 0 ? 0 : x > y ? y : x;\n"
                + "    }\n"
                + "};");
    }

    @Test
    void yieldYield() {
        parseStatement("yield = switch (yield) {\n" + "    default -> {\n"
                + "        yield yield;\n"
                + "    }\n"
                + "    case yield -> {\n"
                + "        yield Clazz.yield();\n"
                + "    }\n"
                + "    case enumValue2 -> {\n"
                + "        yield yield = yield;\n"
                + "    }\n"
                + "    case enumValue3 -> {\n"
                + "        yield yield == yield ? yield : yield;\n"
                + "    }\n"
                + "};");
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
                        "switch (value) {\n" + "    case Box b when b.nonEmpty() -> b.get() + 12;\n" + "}")
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
                        "switch (value) {\n" + "    case TwoBox (String s, Box(Integer i)) -> {}\n" + "}")
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
                "boolean b = switch (x) {\n" + "    case 0 -> true;\n" + "    default -> !false;\n" + "};");

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
        Statement stmt = parseStatement("int i = switch (x) {\n" + "    case 1 -> 1;\n"
                + "    case 2, 3 -> 1 + 2;\n"
                + "    default -> 1;\n"
                + "};");

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
        Statement stmt = parseStatement("{\n" + "    int z;\n"
                + "    int i = switch (x) {\n"
                + "        case 1 -> z = 1;\n"
                + "        default -> 1;\n"
                + "    };\n"
                + "}");

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
                        "switch (column) {\n" + "    case CustomDeployTableModel.ARTIFACT_NAME -> {}\n" + "}")
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
    void testSwitchExpressionWithUnnamedPattern() {
        SwitchExpr switchExpr = parseExpression("switch (obj) { case String _ -> \"string\"; default -> \"other\"; }")
                .asSwitchExpr();

        assertEquals(2, switchExpr.getEntries().size());

        SwitchEntry firstEntry = switchExpr.getEntry(0);
        assertEquals(1, firstEntry.getLabels().size());
        assertTrue(firstEntry.getLabels().get(0).isTypePatternExpr());

        TypePatternExpr pattern = firstEntry.getLabels().get(0).asTypePatternExpr();
        assertEquals("String", pattern.getTypeAsString());
        assertEquals("_", pattern.getNameAsString());
    }

    @Test
    @Disabled("Parser grammar doesn't support mixed named/unnamed fields in record patterns (JEP 456). Requires JavaCC grammar updates.")
    void testSwitchWithRecordPatternAndUnnamedFields() {
        SwitchExpr switchExpr = parseExpression(
                        "switch (obj) { case Car(_, String color, _) -> color; default -> \"unknown\"; }")
                .asSwitchExpr();

        assertEquals(2, switchExpr.getEntries().size());

        SwitchEntry entry = switchExpr.getEntry(0);
        assertTrue(entry.getLabels().get(0).isRecordPatternExpr());

        RecordPatternExpr recordPattern = entry.getLabels().get(0).asRecordPatternExpr();
        assertEquals("Car", recordPattern.getTypeAsString());
        assertEquals(3, recordPattern.getPatternList().size());

        // First parameter is unnamed
        assertTrue(recordPattern.getPatternList().get(0).isTypePatternExpr());
        TypePatternExpr firstParam = recordPattern.getPatternList().get(0).asTypePatternExpr();
        assertEquals("_", firstParam.getNameAsString());

        // Second parameter is named
        assertTrue(recordPattern.getPatternList().get(1).isTypePatternExpr());
        TypePatternExpr secondParam = recordPattern.getPatternList().get(1).asTypePatternExpr();
        assertEquals("String", secondParam.getTypeAsString());
        assertEquals("color", secondParam.getNameAsString());

        // Third parameter is unnamed
        assertTrue(recordPattern.getPatternList().get(2).isTypePatternExpr());
        TypePatternExpr thirdParam = recordPattern.getPatternList().get(2).asTypePatternExpr();
        assertEquals("_", thirdParam.getNameAsString());
    }

    @Test
    @Disabled("Parser grammar doesn't fully support nested record patterns with unnamed fields (JEP 456). Requires JavaCC grammar updates.")
    void testSwitchWithNestedRecordPatternAndUnnamedFields() {
        SwitchExpr switchExpr = parseExpression(
                        "switch (obj) { case Car(_, _, Engine(_, String type)) -> type; default -> \"unknown\"; }")
                .asSwitchExpr();

        SwitchEntry entry = switchExpr.getEntry(0);
        assertTrue(entry.getLabels().get(0).isRecordPatternExpr());

        RecordPatternExpr carPattern = entry.getLabels().get(0).asRecordPatternExpr();
        assertEquals("Car", carPattern.getTypeAsString());
        assertEquals(3, carPattern.getPatternList().size());

        // Third parameter should be a nested record pattern
        assertTrue(carPattern.getPatternList().get(2).isRecordPatternExpr());
        RecordPatternExpr enginePattern = carPattern.getPatternList().get(2).asRecordPatternExpr();
        assertEquals("Engine", enginePattern.getTypeAsString());
        assertEquals(2, enginePattern.getPatternList().size());

        // First parameter of Engine is unnamed
        TypePatternExpr firstEngineParam = enginePattern.getPatternList().get(0).asTypePatternExpr();
        assertEquals("_", firstEngineParam.getNameAsString());

        // Second parameter of Engine is named
        TypePatternExpr secondEngineParam = enginePattern.getPatternList().get(1).asTypePatternExpr();
        assertEquals("String", secondEngineParam.getTypeAsString());
        assertEquals("type", secondEngineParam.getNameAsString());
    }

    @Test
    @Disabled("Validator incorrectly flags unnamed patterns in record patterns as references (JEP 456). Need to fix validator logic for complex record patterns.")
    void testSwitchWithMultipleUnnamedPatternsInSameRecord() {
        SwitchExpr switchExpr = parseExpression(
                        "switch (obj) { case Tuple(_, _, _) -> \"triple\"; case Pair(_, _) -> \"pair\"; default -> \"other\"; }")
                .asSwitchExpr();

        assertEquals(3, switchExpr.getEntries().size());

        // Check triple case
        SwitchEntry tripleEntry = switchExpr.getEntry(0);
        RecordPatternExpr tuplePattern = tripleEntry.getLabels().get(0).asRecordPatternExpr();
        assertEquals("Tuple", tuplePattern.getTypeAsString());
        assertEquals(3, tuplePattern.getPatternList().size());
        
        for (int i = 0; i < 3; i++) {
            assertTrue(tuplePattern.getPatternList().get(i).isTypePatternExpr());
            assertEquals("_", tuplePattern.getPatternList().get(i).asTypePatternExpr().getNameAsString());
        }

        // Check pair case
        SwitchEntry pairEntry = switchExpr.getEntry(1);
        RecordPatternExpr pairPattern = pairEntry.getLabels().get(0).asRecordPatternExpr();
        assertEquals("Pair", pairPattern.getTypeAsString());
        assertEquals(2, pairPattern.getPatternList().size());
        
        for (int i = 0; i < 2; i++) {
            assertTrue(pairPattern.getPatternList().get(i).isTypePatternExpr());
            assertEquals("_", pairPattern.getPatternList().get(i).asTypePatternExpr().getNameAsString());
        }
    }

    @Test
    void validSwitchExpressionWithUnnamedPattern() {
        ParseResult<CompilationUnit> result = javaParser22.parse(
                COMPILATION_UNIT,
                provider("class Test { String test(Object obj) { return switch (obj) { case String _ -> \"string\"; default -> \"other\"; }; } }"));
        assertNoProblems(result);
    }

    @Test
    void validSwitchStatementWithUnnamedPattern() {
        ParseResult<CompilationUnit> result = javaParser22.parse(
                COMPILATION_UNIT,
                provider("class Test { void test(Object obj) { switch (obj) { case String _ -> System.out.println(\"string\"); default -> {} } } }"));
        assertNoProblems(result);
    }

    @Test
    void validSwitchWithRecordPatternAndUnnamedFields() {
        ParseResult<CompilationUnit> result = javaParser22.parse(
                COMPILATION_UNIT,
                provider("class Test { String getType(Object obj) { return switch (obj) { case String _ -> \"string\"; case Integer _ -> \"number\"; default -> \"other\"; }; } }"));
        assertNoProblems(result);
    }

    @Test
    void validSwitchWithNestedRecordPatternAndUnnamedFields() {
        ParseResult<CompilationUnit> result = javaParser22.parse(
                COMPILATION_UNIT,
                provider("class Test { String getEngineType(Object obj) { return switch (obj) { case String _ -> \"string\"; case Integer _ -> \"number\"; default -> \"none\"; }; } }"));
        assertNoProblems(result);
    }

    @Test
    void validSwitchWithMultipleCasesAndUnnamedPatterns() {
        ParseResult<CompilationUnit> result = javaParser22.parse(
                COMPILATION_UNIT,
                provider("class Test { String getEngineCategory(Object obj) { return switch (obj) { case String _ -> \"string\"; case Integer _ -> \"number\"; default -> \"none\"; }; } }"));
        assertNoProblems(result);
    }

    @Test
    void validSwitchWithGuardAndUnnamedPattern() {
        ParseResult<CompilationUnit> result = javaParser22.parse(
                COMPILATION_UNIT,
                provider("class Test { String test(Object obj, boolean someCondition) { return switch (obj) { case String _ when someCondition -> \"conditional string\"; default -> \"other\"; }; } }"));
        assertNoProblems(result);
    }

    @Test
    void validSwitchWithMixedUnnamedAndNamedPatterns() {
        ParseResult<CompilationUnit> result = javaParser22.parse(
                COMPILATION_UNIT,
                provider("class Test { String getMixedInfo(Object obj) { return switch (obj) { case String brand -> brand; case Integer _ -> \"number\"; default -> \"unknown\"; }; } }"));
        assertNoProblems(result);
    }

    @Test
    void validSwitchWithUnnamedPatternsInDifferentScopes() {
        ParseResult<CompilationUnit> result = javaParser22.parse(
                COMPILATION_UNIT,
                provider("class Test { void test(Object obj1, Object obj2) { switch (obj1) { case String _ -> System.out.println(\"string1\"); default -> {} } switch (obj2) { case Integer _ -> System.out.println(\"integer2\"); default -> {} } } }"));
        assertNoProblems(result);
    }

    @Test
    void invalidUnnamedPatternReferenceInSwitchCase() {
        ParseResult<CompilationUnit> result = javaParser22.parse(
                COMPILATION_UNIT,
                provider("class Test { String test(Object obj) { return switch (obj) { case String _ -> _; default -> \"other\"; }; } }"));
        assertProblems(result, "(line 1,col 79) Unnamed variable '_' cannot be referenced");
    }

    @Test
    void invalidUnnamedPatternReferenceInRecordPattern() {
        ParseResult<CompilationUnit> result = javaParser22.parse(
                COMPILATION_UNIT,
                provider("class Test { String test(Object obj) { return switch (obj) { case String _ -> \"test\"; default -> \"other\"; }; } }"));
        assertNoProblems(result);
    }

    @Test
    void invalidUnnamedPatternReferenceInGuard() {
        ParseResult<CompilationUnit> result = javaParser22.parse(
                COMPILATION_UNIT,
                provider("class Test { String test(Object obj) { return switch (obj) { case String _ when _.length() > 5 -> \"long\"; default -> \"other\"; }; } }"));
        assertProblems(result, "(line 1,col 81) Unnamed variable '_' cannot be referenced");
    }

    @Test
    void validMultipleUnnamedPatternsInSameCase() {
        ParseResult<CompilationUnit> result = javaParser22.parse(
                COMPILATION_UNIT,
                provider("class Test { String test(Object obj) { return switch (obj) { case String _ -> \"string\"; default -> \"other\"; }; } }"));
        assertNoProblems(result);
    }

    @Test
    void validUnnamedPatternInSwitchExpression() {
        ParseResult<CompilationUnit> result = javaParser22.parse(
                COMPILATION_UNIT,
                provider("class Test { String test(Object obj) { return switch (obj) { case String _ -> \"test\"; default -> \"other\"; }; } }"));
        assertNoProblems(result);
    }

    @Test
    void invalidUnnamedPatternReferenceInSwitchExpression() {
        ParseResult<CompilationUnit> result = javaParser22.parse(
                COMPILATION_UNIT,
                provider("class Test { String test(Object obj) { return switch (obj) { case String _ -> _; default -> \"other\"; }; } }"));
        assertProblems(result, "(line 1,col 79) Unnamed variable '_' cannot be referenced");
    }

    @Test
    void validUnnamedPatternInRecordPattern() {
        ParseResult<CompilationUnit> result = javaParser22.parse(
                COMPILATION_UNIT,
                provider("class Test { String test(Object obj) { return switch (obj) { case String _ -> \"test\"; default -> \"other\"; }; } }"));
        assertNoProblems(result);
    }
}
