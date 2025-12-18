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
