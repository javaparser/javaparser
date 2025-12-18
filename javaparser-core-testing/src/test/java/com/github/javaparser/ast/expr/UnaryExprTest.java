/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2025 The JavaParser Team.
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

import static com.github.javaparser.StaticJavaParser.parseExpression;
import static com.github.javaparser.StaticJavaParser.parseStatement;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.stmt.AssertStmt;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.Statement;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

class UnaryExprTest {
    @BeforeEach
    void initParser() {
        StaticJavaParser.setConfiguration(new ParserConfiguration());
    }

    @Test
    void unaryPlusTest() {
        Expression e = parseExpression("+x");
        assertInstanceOf(UnaryExpr.class, e);
        UnaryExpr unary = e.asUnaryExpr();
        assertEquals(UnaryExpr.Operator.PLUS, unary.getOperator());

        assertInstanceOf(NameExpr.class, unary.getExpression());
        assertEquals("x", unary.getExpression().asNameExpr().getNameAsString());
    }

    @Test
    void unaryMinusTest() {
        Expression e = parseExpression("-x");
        assertInstanceOf(UnaryExpr.class, e);
        UnaryExpr unary = e.asUnaryExpr();
        assertEquals(UnaryExpr.Operator.MINUS, unary.getOperator());

        assertInstanceOf(NameExpr.class, unary.getExpression());
        assertEquals("x", unary.getExpression().asNameExpr().getNameAsString());
    }

    @Test
    void prefixIncrementTest() {
        Expression e = parseExpression("++x");
        assertInstanceOf(UnaryExpr.class, e);
        UnaryExpr unary = e.asUnaryExpr();
        assertEquals(UnaryExpr.Operator.PREFIX_INCREMENT, unary.getOperator());

        assertInstanceOf(NameExpr.class, unary.getExpression());
        assertEquals("x", unary.getExpression().asNameExpr().getNameAsString());
    }

    @Test
    void prefixDecrementTest() {
        Expression e = parseExpression("--x");
        assertInstanceOf(UnaryExpr.class, e);
        UnaryExpr unary = e.asUnaryExpr();
        assertEquals(UnaryExpr.Operator.PREFIX_DECREMENT, unary.getOperator());

        assertInstanceOf(NameExpr.class, unary.getExpression());
        assertEquals("x", unary.getExpression().asNameExpr().getNameAsString());
    }

    @Test
    void logicalComplementTest() {
        Expression e = parseExpression("!flag");
        assertInstanceOf(UnaryExpr.class, e);
        UnaryExpr unary = e.asUnaryExpr();
        assertEquals(UnaryExpr.Operator.LOGICAL_COMPLEMENT, unary.getOperator());

        assertInstanceOf(NameExpr.class, unary.getExpression());
        assertEquals("flag", unary.getExpression().asNameExpr().getNameAsString());
    }

    @Test
    void bitwiseComplementTest() {
        Expression e = parseExpression("~x");
        assertInstanceOf(UnaryExpr.class, e);
        UnaryExpr unary = e.asUnaryExpr();
        assertEquals(UnaryExpr.Operator.BITWISE_COMPLEMENT, unary.getOperator());

        assertInstanceOf(NameExpr.class, unary.getExpression());
        assertEquals("x", unary.getExpression().asNameExpr().getNameAsString());
    }

    @Test
    void postfixIncrementTest() {
        Expression e = parseExpression("x++");
        assertInstanceOf(UnaryExpr.class, e);
        UnaryExpr unary = e.asUnaryExpr();
        assertEquals(UnaryExpr.Operator.POSTFIX_INCREMENT, unary.getOperator());

        assertInstanceOf(NameExpr.class, unary.getExpression());
        assertEquals("x", unary.getExpression().asNameExpr().getNameAsString());
    }

    @Test
    void postfixDecrementTest() {
        Expression e = parseExpression("x--");
        assertInstanceOf(UnaryExpr.class, e);
        UnaryExpr unary = e.asUnaryExpr();
        assertEquals(UnaryExpr.Operator.POSTFIX_DECREMENT, unary.getOperator());

        assertInstanceOf(NameExpr.class, unary.getExpression());
        assertEquals("x", unary.getExpression().asNameExpr().getNameAsString());
    }

    @Test
    void nestedUnaryTest() {
        Expression e = parseExpression("!!flag");
        assertInstanceOf(UnaryExpr.class, e);
        UnaryExpr outerUnary = e.asUnaryExpr();
        assertEquals(UnaryExpr.Operator.LOGICAL_COMPLEMENT, outerUnary.getOperator());

        assertInstanceOf(UnaryExpr.class, outerUnary.getExpression());
        UnaryExpr innerUnary = outerUnary.getExpression().asUnaryExpr();
        assertEquals(UnaryExpr.Operator.LOGICAL_COMPLEMENT, innerUnary.getOperator());

        assertInstanceOf(NameExpr.class, innerUnary.getExpression());
        assertEquals("flag", innerUnary.getExpression().asNameExpr().getNameAsString());
    }

    @Test
    void unaryWithMethodCallTest() {
        Expression e = parseExpression("!obj.isValid()");
        assertInstanceOf(UnaryExpr.class, e);
        UnaryExpr unary = e.asUnaryExpr();
        assertEquals(UnaryExpr.Operator.LOGICAL_COMPLEMENT, unary.getOperator());

        assertInstanceOf(MethodCallExpr.class, unary.getExpression());
        MethodCallExpr methodCall = unary.getExpression().asMethodCallExpr();
        assertEquals("isValid", methodCall.getNameAsString());

        assertInstanceOf(NameExpr.class, methodCall.getScope().get());
        assertEquals("obj", methodCall.getScope().get().asNameExpr().getNameAsString());
    }

    @Test
    void unaryWithArrayAccessTest() {
        Expression e = parseExpression("++array[i]");
        assertInstanceOf(UnaryExpr.class, e);
        UnaryExpr unary = e.asUnaryExpr();
        assertEquals(UnaryExpr.Operator.PREFIX_INCREMENT, unary.getOperator());

        assertInstanceOf(ArrayAccessExpr.class, unary.getExpression());
        ArrayAccessExpr arrayAccess = unary.getExpression().asArrayAccessExpr();

        assertInstanceOf(NameExpr.class, arrayAccess.getName());
        assertEquals("array", arrayAccess.getName().asNameExpr().getNameAsString());

        assertInstanceOf(NameExpr.class, arrayAccess.getIndex());
        assertEquals("i", arrayAccess.getIndex().asNameExpr().getNameAsString());
    }

    @Test
    void unaryWithFieldAccessTest() {
        Expression e = parseExpression("-obj.value");
        assertInstanceOf(UnaryExpr.class, e);
        UnaryExpr unary = e.asUnaryExpr();
        assertEquals(UnaryExpr.Operator.MINUS, unary.getOperator());

        assertInstanceOf(FieldAccessExpr.class, unary.getExpression());
        FieldAccessExpr fieldAccess = unary.getExpression().asFieldAccessExpr();
        assertEquals("value", fieldAccess.getNameAsString());

        assertInstanceOf(NameExpr.class, fieldAccess.getScope());
        assertEquals("obj", fieldAccess.getScope().asNameExpr().getNameAsString());
    }

    @Test
    void mixedPrefixAndPostfixTest() {
        Expression e = parseExpression("++(x--)");
        assertInstanceOf(UnaryExpr.class, e);
        UnaryExpr prefixUnary = e.asUnaryExpr();
        assertEquals(UnaryExpr.Operator.PREFIX_INCREMENT, prefixUnary.getOperator());

        assertInstanceOf(EnclosedExpr.class, prefixUnary.getExpression());
        EnclosedExpr enclosed = prefixUnary.getExpression().asEnclosedExpr();

        assertInstanceOf(UnaryExpr.class, enclosed.getInner());
        UnaryExpr postfixUnary = enclosed.getInner().asUnaryExpr();
        assertEquals(UnaryExpr.Operator.POSTFIX_DECREMENT, postfixUnary.getOperator());

        assertInstanceOf(NameExpr.class, postfixUnary.getExpression());
        assertEquals("x", postfixUnary.getExpression().asNameExpr().getNameAsString());
    }

    @Test
    void unaryInBinaryExprTest() {
        Expression e = parseExpression("-x + y");
        assertInstanceOf(BinaryExpr.class, e);
        BinaryExpr binary = e.asBinaryExpr();
        assertEquals(BinaryExpr.Operator.PLUS, binary.getOperator());

        assertInstanceOf(UnaryExpr.class, binary.getLeft());
        UnaryExpr unary = binary.getLeft().asUnaryExpr();
        assertEquals(UnaryExpr.Operator.MINUS, unary.getOperator());
        assertEquals("x", unary.getExpression().asNameExpr().getNameAsString());

        assertInstanceOf(NameExpr.class, binary.getRight());
        assertEquals("y", binary.getRight().asNameExpr().getNameAsString());
    }

    @Test
    void unaryInAssertStatementTest() {
        Statement stmt = parseStatement("assert ++counter == 1 : \"Counter should be incremented\";");
        assertInstanceOf(AssertStmt.class, stmt);
        AssertStmt assertStmt = stmt.asAssertStmt();

        assertInstanceOf(BinaryExpr.class, assertStmt.getCheck());
        BinaryExpr condition = assertStmt.getCheck().asBinaryExpr();
        assertEquals(BinaryExpr.Operator.EQUALS, condition.getOperator());

        assertInstanceOf(UnaryExpr.class, condition.getLeft());
        UnaryExpr unary = condition.getLeft().asUnaryExpr();
        assertEquals(UnaryExpr.Operator.PREFIX_INCREMENT, unary.getOperator());

        assertInstanceOf(NameExpr.class, unary.getExpression());
        assertEquals("counter", unary.getExpression().asNameExpr().getNameAsString());

        assertInstanceOf(IntegerLiteralExpr.class, condition.getRight());
        assertEquals("1", condition.getRight().asIntegerLiteralExpr().getValue());

        assertInstanceOf(StringLiteralExpr.class, assertStmt.getMessage().get());
        assertEquals(
                "Counter should be incremented",
                assertStmt.getMessage().get().asStringLiteralExpr().getValue());
    }

    @Test
    void postfixIncrementOnAssertIdentifierTest() {
        // Note: "assert" as an identifier is only valid in Java < 1.4 In modern Java,
        // "assert" is a keyword. However, "assert" as an identifier is still supported
        // for backward compatibility
        StaticJavaParser.getParserConfiguration().setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_1_0);

        Statement stmt = parseStatement("assert++;");
        assertInstanceOf(ExpressionStmt.class, stmt);
        ExpressionStmt exprStmt = stmt.asExpressionStmt();

        assertInstanceOf(UnaryExpr.class, exprStmt.getExpression());
        UnaryExpr unary = exprStmt.getExpression().asUnaryExpr();
        assertEquals(UnaryExpr.Operator.POSTFIX_INCREMENT, unary.getOperator());

        assertInstanceOf(NameExpr.class, unary.getExpression());
        assertEquals("assert", unary.getExpression().asNameExpr().getNameAsString());
    }

    @Test
    void prefixIncrementOnAssertIdentifierTest() {
        // Note: "assert" as an identifier is only valid in Java < 1.4 In modern Java,
        // "assert" is a keyword. However, "assert" as an identifier is still supported
        // for backward compatibility
        StaticJavaParser.getParserConfiguration().setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_1_0);

        Statement stmt = parseStatement("++assert;");
        assertInstanceOf(ExpressionStmt.class, stmt);
        ExpressionStmt exprStmt = stmt.asExpressionStmt();

        assertInstanceOf(UnaryExpr.class, exprStmt.getExpression());
        UnaryExpr unary = exprStmt.getExpression().asUnaryExpr();
        assertEquals(UnaryExpr.Operator.PREFIX_INCREMENT, unary.getOperator());

        assertInstanceOf(NameExpr.class, unary.getExpression());
        assertEquals("assert", unary.getExpression().asNameExpr().getNameAsString());
    }
}
