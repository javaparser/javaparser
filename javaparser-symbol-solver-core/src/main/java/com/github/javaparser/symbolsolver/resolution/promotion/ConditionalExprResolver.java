/*
 * Copyright (C) 2013-2023 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.resolution.promotion;

import com.github.javaparser.resolution.promotion.ConditionalExprHandler;
import com.github.javaparser.resolution.types.ResolvedPrimitiveType;
import com.github.javaparser.resolution.types.ResolvedType;

/*
 * The conditional operator has three operand expressions.
 * ? appears between the first and second expressions,
 * and : appears between the second and third expressions.
 * There are three kinds of conditional expressions, classified according to the second and third operand expressions: boolean conditional expressions, numeric conditional expressions, and reference conditional expressions.
 * The classification rules are as follows:
 * 1/ If both the second and the third operand expressions are boolean expressions, the conditional expression is a boolean conditional expression.
 * 2/ If both the second and the third operand expressions are numeric expressions, the conditional expression is a numeric conditional expression.
 * 3/ Otherwise, the conditional expression is a reference conditional expression
 */
public class ConditionalExprResolver {
    private static final ResolvedPrimitiveType TYPE_BOOLEAN = ResolvedPrimitiveType.BOOLEAN;

    public static ConditionalExprHandler getConditionExprHandler(ResolvedType thenExpr, ResolvedType elseExpr) {
        // boolean conditional expressions
        if (!thenExpr.isNull() && !elseExpr.isNull()
                && thenExpr.isAssignableBy(TYPE_BOOLEAN) && elseExpr.isAssignableBy(TYPE_BOOLEAN)) {
            return new BooleanConditionalExprHandler(thenExpr, elseExpr);
            // numeric conditional expressions
        }
        if (thenExpr.isNumericType() && elseExpr.isNumericType()) {
            return new NumericConditionalExprHandler(thenExpr, elseExpr);
        }
        // reference conditional expressions
        return new ReferenceConditionalExprHandler(thenExpr, elseExpr);
    }
}
