/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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

import com.github.javaparser.StaticJavaParser;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

class BinaryExprTest {

    @Test
    void convertOperator() {
        assertEquals(AssignExpr.Operator.PLUS, BinaryExpr.Operator.PLUS.toAssignOperator().get());
    }

    /**
     * Evaluation takes place left to right, with && taking precedence over ||
     *
     * true || false && false || false
     * true ||      (1)       || false
     * (        2           ) || false
     * (             3               )
     *
     * true || false && false || false
     * true ||    (false)     || false
     * (     true           ) || false
     * (           true              )
     */
    @Nested
    class LogicalOperatorPrecedence {

        @Test
        public void logicalAndOr() {
            Expression expression = StaticJavaParser.parseExpression("true || false && false || false");
            Expression bracketedExpression = applyBrackets(expression);

            String expected = "(true || (false && false)) || false";
            String actual = bracketedExpression.toString();

            assertEquals(expected, actual);
        }

        @Test
        public void logicalOrEvaluationLeftToRight() {
            Expression expression = StaticJavaParser.parseExpression("false || true || false || true || false || true");
            Expression bracketedExpression = applyBrackets(expression);

            String expected = "((((false || true) || false) || true) || false) || true";
            String actual = bracketedExpression.toString();

            assertEquals(expected, actual);
        }

        @Test
        public void logicalAndEvaluationLeftToRight() {
            Expression expression = StaticJavaParser.parseExpression("false && true && false && true && false && true");
            Expression bracketedExpression = applyBrackets(expression);

            String expected = "((((false && true) && false) && true) && false) && true";
            String actual = bracketedExpression.toString();

            assertEquals(expected, actual);
        }

        @Test
        public void andTakesPrecedenceOverOr() {
            Expression expression = StaticJavaParser.parseExpression("true || false && false");
            Expression bracketedExpression = applyBrackets(expression);

            String expected = "true || (false && false)";
            String actual = bracketedExpression.toString();

            assertEquals(expected, actual);
        }

        @Test
        public void andTakesPrecedenceOverOrThenLeftToRight() {
            Expression expression = StaticJavaParser.parseExpression("true || false && false || true");
            Expression bracketedExpression = applyBrackets(expression);

            String expected = "(true || (false && false)) || true";
            String actual = bracketedExpression.toString();

            assertEquals(expected, actual);
        }


        @Test
        public void example() {
            Expression expression = StaticJavaParser.parseExpression("year % 4 == 0 && year % 100 != 0 || year % 400 == 0");
            Expression bracketedExpression = applyBrackets(expression);

            String expected = "((year % 4 == 0) && (year % 100 != 0)) || (year % 400 == 0)";
            String actual = bracketedExpression.toString();

            assertEquals(expected, actual);
        }


    }


    private Expression applyBrackets(Expression expression) {
        expression.findAll(BinaryExpr.class)
                .stream()
                .filter(binaryExpr -> binaryExpr.getOperator() == BinaryExpr.Operator.AND || binaryExpr.getOperator() == BinaryExpr.Operator.OR)
                .forEach(binaryExpr -> {
                    if(!binaryExpr.getLeft().isBooleanLiteralExpr()) {
                        binaryExpr.setLeft(new EnclosedExpr(binaryExpr.getLeft()));
                    }
                    if(!binaryExpr.getRight().isBooleanLiteralExpr()) {
                        binaryExpr.setRight(new EnclosedExpr(binaryExpr.getRight()));
                    }
                });

        return expression;
    }
}
