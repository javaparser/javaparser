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

import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.UnaryExpr;

/**
 * Keeps a prefix sign from merging with the leading sign of its operand.
 */
final class UnaryOperatorSeparation {

    private UnaryOperatorSeparation() {}

    static boolean isRequired(UnaryExpr expression) {
        UnaryExpr.Operator operator = expression.getOperator();
        if (operator != UnaryExpr.Operator.PLUS && operator != UnaryExpr.Operator.MINUS) {
            return false;
        }
        Expression operand = expression.getExpression();
        String leadingText;
        if (operand.isUnaryExpr() && operand.asUnaryExpr().isPrefix()) {
            leadingText = operand.asUnaryExpr().getOperator().asString();
        } else if (operand.isIntegerLiteralExpr()) {
            leadingText = operand.asIntegerLiteralExpr().getValue();
        } else if (operand.isLongLiteralExpr()) {
            leadingText = operand.asLongLiteralExpr().getValue();
        } else if (operand.isDoubleLiteralExpr()) {
            leadingText = operand.asDoubleLiteralExpr().getValue();
        } else {
            return false;
        }
        return leadingText.startsWith(operator.asString());
    }
}
