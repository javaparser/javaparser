package com.github.javaparser.symbolsolver.resolution.promotion;

import com.github.javaparser.resolution.types.ResolvedType;

public class ReferenceConditionalExprHandler implements ConditionalExprHandler {
    ResolvedType thenExpr;
    ResolvedType elseExpr;

    public ReferenceConditionalExprHandler(ResolvedType thenExpr, ResolvedType elseExpr) {
        this.thenExpr = thenExpr;
        this.elseExpr = elseExpr;
    }

    @Override
    public ResolvedType resolveType() {
        // If one of the second and third operands is of the null type and the type of the other is a reference type, then the type of the conditional expression is that reference type.
        if (thenExpr.isNull()) {
            return elseExpr;
        }
        if (elseExpr.isNull()) {
            return thenExpr;
        }
        throw new UnsupportedOperationException("resolving a reference conditional expression");
    }
}