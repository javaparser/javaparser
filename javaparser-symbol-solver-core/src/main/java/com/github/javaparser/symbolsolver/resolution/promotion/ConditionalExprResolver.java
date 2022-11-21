package com.github.javaparser.symbolsolver.resolution.promotion;

import com.github.javaparser.resolution.types.ResolvedPrimitiveType;
import com.github.javaparser.resolution.types.ResolvedType;

/*
 * The conditional operator has three operand expressions. ? appears between the first and second expressions, and : appears between the second and third expressions.
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
