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

import java.util.Arrays;
import java.util.HashSet;

import com.github.javaparser.resolution.promotion.ConditionalExprHandler;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.resolution.typeinference.TypeHelper;

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
        return TypeHelper.leastUpperBound(new HashSet<>(Arrays.asList(thenExpr, elseExpr)));
    }
}