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
import com.github.javaparser.resolution.types.ResolvedType;

/*
 * Boolean conditional expressions are standalone expressions
 * The type of a boolean conditional expression is determined as follows:
 * If the second and third operands are both of type Boolean, the conditional expression has type Boolean.
 * Otherwise, the conditional expression has type boolean.
 */
public class BooleanConditionalExprHandler implements ConditionalExprHandler {
    ResolvedType thenExpr;
    ResolvedType elseExpr;

    public BooleanConditionalExprHandler(ResolvedType thenExpr, ResolvedType elseExpr) {
        this.thenExpr = thenExpr;
        this.elseExpr = elseExpr;
    }
    
    @Override
    public ResolvedType resolveType() {
        if (thenExpr.isReferenceType() && elseExpr.isReferenceType()) {
            return thenExpr.asReferenceType();
        }
        return thenExpr.isPrimitive() ? thenExpr : elseExpr;
    }
}