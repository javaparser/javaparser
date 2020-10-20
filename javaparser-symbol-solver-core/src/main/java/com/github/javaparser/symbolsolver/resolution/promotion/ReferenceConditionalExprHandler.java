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
        throw new UnsupportedOperationException("resolving a reference conditional expression");
    }
}
