/*
 * Copyright (C) 2013-2026 The JavaParser Team.
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
package com.github.javaparser.printer;

import static com.github.javaparser.StaticJavaParser.parse;
import static com.github.javaparser.ast.expr.UnaryExpr.Operator.*;
import static org.junit.jupiter.api.Assertions.assertEquals;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.printer.lexicalpreservation.LexicalPreservingPrinter;
import java.util.stream.Stream;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;
import org.junit.jupiter.params.provider.ValueSource;

class UnaryOperatorSeparationTest {
    static Stream<Arguments> signedLiterals() {
        return Stream.of(
                Arguments.of(new IntegerLiteralExpr(-5), MINUS, "- -5"),
                Arguments.of(new LongLiteralExpr(-5L), MINUS, "- -5"),
                Arguments.of(new LongLiteralExpr("-5L"), MINUS, "- -5L"),
                Arguments.of(new DoubleLiteralExpr(-1.5), MINUS, "- -1.5"),
                Arguments.of(new DoubleLiteralExpr(-0.0), MINUS, "- -0.0"),
                Arguments.of(new IntegerLiteralExpr("+5"), PLUS, "+ +5"),
                Arguments.of(new LongLiteralExpr("+5L"), PLUS, "+ +5L"),
                Arguments.of(new DoubleLiteralExpr("+1.5"), PLUS, "+ +1.5"),
                Arguments.of(new IntegerLiteralExpr(-5), PLUS, "+-5"),
                Arguments.of(new IntegerLiteralExpr("+5"), MINUS, "-+5"));
    }

    @ParameterizedTest
    @MethodSource("signedLiterals")
    void prettyPrintersSeparateSignedApiLiterals(Expression operand, UnaryExpr.Operator operator, String expected) {
        UnaryExpr expression = new UnaryExpr(operand, operator);
        assertEquals(expected, new DefaultPrettyPrinter().print(expression));
        assertEquals(expected, new PrettyPrinter().print(expression));
    }

    @ParameterizedTest
    @MethodSource("signedLiterals")
    void lexicalPrinterSeparatesSignedApiLiterals(Expression operand, UnaryExpr.Operator operator, String expected) {
        CompilationUnit cu = source(operator.asString() + "x");
        cu.findFirst(UnaryExpr.class).get().setExpression(operand);
        assertEquals(code(expected), LexicalPreservingPrinter.print(cu));
    }

    @ParameterizedTest
    @ValueSource(strings = {"-", "+"})
    void lexicalPrinterSeparatesReplacedOperand(String sign) {
        CompilationUnit cu = source(sign + "x");
        UnaryExpr.Operator operator = "-".equals(sign) ? MINUS : PLUS;
        cu.findFirst(UnaryExpr.class).get().setExpression(new UnaryExpr(new NameExpr("x"), operator));
        assertEquals(code(sign + " " + sign + "x"), LexicalPreservingPrinter.print(cu));
    }

    @ParameterizedTest
    @ValueSource(strings = {"-", "+"})
    void lexicalPrinterSeparatesWrappedIncrementOrDecrement(String sign) {
        CompilationUnit cu = source(sign + sign + "x");
        ReturnStmt statement = cu.findFirst(ReturnStmt.class).get();
        Expression original = statement.getExpression().get();
        statement.setExpression(new UnaryExpr(original.clone(), "-".equals(sign) ? MINUS : PLUS));
        assertEquals(code(sign + " " + sign + sign + "x"), LexicalPreservingPrinter.print(cu));
    }

    @ParameterizedTest
    @ValueSource(strings = {"-", "+"})
    void lexicalPrinterSeparatesChangedInnerOperator(String sign) {
        CompilationUnit cu = source(sign + "!x");
        cu.findFirst(UnaryExpr.class).get().getExpression().asUnaryExpr().setOperator("-".equals(sign) ? MINUS : PLUS);
        assertEquals(code(sign + " " + sign + "x"), LexicalPreservingPrinter.print(cu));
    }

    @ParameterizedTest
    @ValueSource(strings = {"x---y", "x+++y", "- -x", "-(-x)", "+ +x", "+(+x)", "-/*comment*/-x"})
    void lexicalPrinterPreservesExistingTokensAndSiblingEdits(String expression) {
        CompilationUnit cu = source(expression);
        assertEquals(code(expression), LexicalPreservingPrinter.print(cu));
        cu.getClassByName("A").get().setName("B");
        assertEquals(code(expression).replace("class A", "class B"), LexicalPreservingPrinter.print(cu));
    }

    private static CompilationUnit source(String expression) {
        return LexicalPreservingPrinter.setup(parse(code(expression)));
    }

    private static String code(String expression) {
        return "class A { int f(int x, int y) { return " + expression + "; } }";
    }
}
