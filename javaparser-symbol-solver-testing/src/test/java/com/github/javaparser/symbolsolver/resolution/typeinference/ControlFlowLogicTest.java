/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2026 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.resolution.typeinference;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.CompactConstructorDeclaration;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.body.InitializerDeclaration;
import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.Statement;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import org.junit.jupiter.params.provider.ValueSource;

class ControlFlowLogicTest {
    private final ControlFlowLogic logic = ControlFlowLogic.getInstance();
    private final JavaParser parser =
            new JavaParser(new ParserConfiguration().setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_17));

    private CompilationUnit parse(String code) {
        ParseResult<CompilationUnit> result = parser.parse(code);
        assertTrue(result.isSuccessful(), () -> "Parse failed: " + result.getProblems());
        return result.getResult().get();
    }

    private BlockStmt body(String statements) {
        return parse("class X { void m() { " + statements + " } }")
                .getClassByName("X")
                .get()
                .getMethodsByName("m")
                .get(0)
                .getBody()
                .get();
    }

    @ParameterizedTest
    @ValueSource(strings = {"int i = 0;", "class L {}", "record R(int a) {}", "enum E { A }"})
    void declarationsAreReachableAndCompleteNormally(String declaration) {
        Statement statement = body(declaration).getStatement(0);
        assertTrue(logic.isReachable(statement));
        assertTrue(logic.canCompleteNormally(statement));
    }

    @Test
    void statementAfterReturnIsUnreachable() {
        Statement statement = body("return; int i = 0;").getStatement(1);
        assertFalse(logic.isReachable(statement));
        assertFalse(logic.canCompleteNormally(statement));
    }

    @Test
    void equalStatementsAreLocatedByIdentity() {
        Statement secondEmpty = body("; return; ;").getStatement(2);
        assertFalse(logic.isReachable(secondEmpty));
        assertFalse(logic.canCompleteNormally(secondEmpty));
    }

    @Test
    void nestedBlockCanCompleteNormally() {
        Statement nested = body("{ int i = 0; }").getStatement(0);
        assertTrue(logic.isReachable(nested));
        assertTrue(logic.canCompleteNormally(nested));
    }

    @Test
    void falseIfConditionDoesNotMakeThenStatementUnreachable() {
        Statement declaration = body("if (false) { int i = 0; }")
                .getStatement(0)
                .asIfStmt()
                .getThenStmt()
                .asBlockStmt()
                .getStatement(0);
        assertTrue(logic.isReachable(declaration));
    }

    @Test
    void lambdaBlockReturningAValueDoesNotCompleteNormally() {
        LambdaExpr lambda = parse(
                        "class X { Object value = (java.util.function.Supplier<Integer>) () -> { return 1; }; }")
                .findFirst(LambdaExpr.class)
                .get();
        assertTrue(logic.isReachable(lambda.getBody()));
        assertFalse(logic.canCompleteNormally(lambda.getBody()));
    }

    @Test
    void infiniteLoopCannotCompleteNormally() {
        assertFalse(logic.canCompleteNormally(body("while (true) {}").getStatement(0)));
    }

    @Test
    void nestedInfiniteLoopPropagatesThroughIf() {
        Statement statement =
                body("if (true) { while (true) {} } else { return; }").getStatement(0);
        assertFalse(logic.canCompleteNormally(statement));
    }

    @Test
    void localClassMethodDoesNotAffectTheEnclosingBlock() {
        BlockStmt block = body("class L { void method() { while (true) {} } }");
        assertTrue(logic.canCompleteNormally(block));
    }

    @ParameterizedTest
    @ValueSource(strings = {"int i = 0;", "class L {}", "record R(int a) {}", "enum E { A }"})
    void declarationsAfterReturnAreUnreachable(String declaration) {
        Statement statement = body("return; " + declaration).getStatement(1);
        assertFalse(logic.isReachable(statement));
        assertFalse(logic.canCompleteNormally(statement));
    }

    @Test
    void methodConstructorAndInitializerBodiesAreEntryPoints() {
        CompilationUnit unit = parse("class X { X() { super(); } { ; } static { ; } void m() {} }");
        BlockStmt constructor =
                unit.findFirst(ConstructorDeclaration.class).get().getBody();
        assertTrue(logic.isReachable(constructor));
        assertTrue(logic.canCompleteNormally(constructor));
        assertTrue(logic.canCompleteNormally(constructor.getStatement(0)));
        for (InitializerDeclaration initializer : unit.findAll(InitializerDeclaration.class)) {
            assertTrue(logic.isReachable(initializer.getBody()));
            assertTrue(logic.canCompleteNormally(initializer.getBody()));
        }
        assertTrue(logic.isReachable(body("")));
        assertTrue(logic.canCompleteNormally(body("")));
    }

    @Test
    void compactConstructorBodyIsAnEntryPoint() {
        BlockStmt compact = parse("record X(int value) { X { if (value < 0) throw new IllegalArgumentException(); } }")
                .findFirst(CompactConstructorDeclaration.class)
                .get()
                .getBody();
        assertTrue(logic.isReachable(compact));
        assertTrue(logic.canCompleteNormally(compact));
    }

    @Test
    void lambdaBodyCanCompleteNormallyWithoutAffectingItsEnclosingBlock() {
        BlockStmt enclosing = body("Runnable r = () -> { return; }; int i = 0;");
        assertTrue(logic.canCompleteNormally(enclosing));
        LambdaExpr abrupt = enclosing.findFirst(LambdaExpr.class).get();
        assertTrue(logic.isReachable(abrupt.getBody()));
        assertFalse(logic.canCompleteNormally(abrupt.getBody()));
        LambdaExpr normal = body("Runnable r = () -> { int i = 0; };")
                .findFirst(LambdaExpr.class)
                .get();
        assertTrue(logic.isReachable(normal.getBody()));
        assertTrue(logic.canCompleteNormally(normal.getBody()));
    }

    @Test
    void ifBranchesUseStructuralReachabilityAndNormalCompletion() {
        Statement bothAbrupt = body("if (true) { return; } else { throw new RuntimeException(); }")
                .getStatement(0);
        assertFalse(logic.canCompleteNormally(bothAbrupt));
        assertTrue(logic.isReachable(bothAbrupt.asIfStmt().getElseStmt().get()));
        Statement oneNormal = body("if (false) { return; } else { ; }").getStatement(0);
        assertTrue(logic.canCompleteNormally(oneNormal));
        assertTrue(logic.canCompleteNormally(body("if (true) { return; }").getStatement(0)));
    }

    @Test
    void synchronizedBodyPropagatesReachabilityAndAbruptCompletion() {
        Statement normal = body("synchronized (this) { ; }").getStatement(0);
        assertTrue(logic.isReachable(normal.asSynchronizedStmt().getBody()));
        assertTrue(logic.canCompleteNormally(normal));
        Statement abrupt = body("synchronized (this) { return; }").getStatement(0);
        assertFalse(logic.canCompleteNormally(abrupt));
        Statement unreachable = body("return; synchronized (this) { ; }").getStatement(1);
        assertFalse(logic.isReachable(unreachable.asSynchronizedStmt().getBody()));
    }

    @Test
    void enhancedForBodyIsReachableButDoesNotHaveToExecute() {
        Statement loop = body("for (String value : new String[0]) { return; }").getStatement(0);
        assertTrue(logic.canCompleteNormally(loop));
        Statement child = loop.asForEachStmt().getBody();
        assertTrue(logic.isReachable(child));
        assertFalse(logic.canCompleteNormally(child));
        assertTrue(logic.canCompleteNormally(
                body("for (String value : new String[0]) { while (true) {} }").getStatement(0)));
    }

    @ParameterizedTest
    @CsvSource(
            delimiter = '|',
            value = {
                "while (true) {}|false",
                "while ((true)) {}|false",
                "while (true) { break; }|true",
                "while (System.nanoTime() > 0) {}|true",
                // Known limitation: JLS 15.29 makes 1 < 2 a constant expression, so javac treats this loop as
                // non-completing. Only the literal true is recognised, hence true is expected here.
                "while (1 < 2) {}|true",
                "do {} while (true);|false",
                "do { break; } while (true);|true",
                "do { continue; } while (false);|true",
                "do { return; } while (false);|false",
                "do { return; } while (System.nanoTime() > 0);|false",
                "for (;;) {}|false",
                "for (;true;) {}|false",
                "for (;;) { break; }|true",
                "for (int i = 0; i < 3; i++) {}|true",
                "for (;;) { while (true) { break; } }|false",
                "while (true) { Runnable r = () -> { for (;;) { break; } }; }|false",
                "while (true) { class L { void m() { while (true) { break; } } } }|false",
                "while (true) { Object o = new Object() { void m() { switch (0) { default: break; } } }; }|false",
                "outer: while (true) { while (true) { break outer; } }|true",
                "try {} finally {}|true",
                "switch (0) { default: break; }|true",
                "label: { break label; }|true"
            })
    void loopsFollowTheJlsRulesForLiteralConditions(String source, boolean completesNormally) {
        Statement statement = body(source).getStatement(0);
        assertTrue(logic.isReachable(statement));
        assertEquals(completesNormally, logic.canCompleteNormally(statement));
    }

    @Test
    void unsupportedParentContextsAreReportedInsteadOfUnboxedNull() {
        Statement loopBody =
                body("while (true) { ; }").getStatement(0).asWhileStmt().getBody();
        UnsupportedOperationException loopFailure =
                assertThrows(UnsupportedOperationException.class, () -> logic.isReachable(loopBody));
        assertTrue(loopFailure.getMessage().contains("BlockStmt under WhileStmt"));
        BlockStmt catchBody = body("try {} catch (RuntimeException failure) { ; }")
                .getStatement(0)
                .asTryStmt()
                .getCatchClauses()
                .get(0)
                .getBody();
        UnsupportedOperationException catchFailure =
                assertThrows(UnsupportedOperationException.class, () -> logic.canCompleteNormally(catchBody));
        assertTrue(catchFailure.getMessage().contains("BlockStmt under CatchClause"));
    }

    @ParameterizedTest
    @ValueSource(
            strings = {
                "int x = switch (k) { case 1 -> { int y = 0; yield y; } default -> 0; };",
                "return switch (k) { case 1 -> { int y = 0; yield y; } default -> 0; };",
                "foo(switch (k) { case 1 -> { int y = 0; yield y; } default -> 0; });"
            })
    void statementsInsideSwitchExpressionAreReachable(String source) {
        BlockStmt block = body("int k = 0; " + source);
        Statement inner = block.findFirst(com.github.javaparser.ast.expr.SwitchExpr.class)
                .get()
                .getEntry(0)
                .getStatements()
                .get(0)
                .asBlockStmt()
                .getStatement(0);
        assertTrue(logic.isReachable(inner));
        assertTrue(logic.canCompleteNormally(inner));
    }

    @Test
    void detachedStatementsRequireAContext() {
        UnsupportedOperationException failure =
                assertThrows(UnsupportedOperationException.class, () -> logic.isReachable(new BlockStmt()));
        assertTrue(failure.getMessage().contains("enclosing AST context for BlockStmt"));
    }
}
