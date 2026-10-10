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

package com.github.javaparser.symbolsolver.resolution.promotion;

import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.promotion.ConditionalExprHandler;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.resolution.typeinference.LeastUpperBoundLogic;
import java.util.Arrays;
import java.util.HashSet;

public class ReferenceConditionalExprHandler implements ConditionalExprHandler {
    ResolvedType thenExpr;
    ResolvedType elseExpr;
    TypeSolver typeSolver;

    public ReferenceConditionalExprHandler(ResolvedType thenExpr, ResolvedType elseExpr) {
        this(thenExpr, elseExpr, null);
    }

    /**
     * @param typeSolver used to solve java.lang.Object, the lub of an interface and a type not implementing it, may
     *     be null
     */
    public ReferenceConditionalExprHandler(ResolvedType thenExpr, ResolvedType elseExpr, TypeSolver typeSolver) {
        this.thenExpr = thenExpr;
        this.elseExpr = elseExpr;
        this.typeSolver = typeSolver;
    }

    @Override
    public ResolvedType resolveType() {
        // If one of the second and third operands is of the null type and the type of the other is a reference type,
        // then the type of the conditional expression is that reference type.
        if (thenExpr.isNull()) {
            return elseExpr;
        }
        if (elseExpr.isNull()) {
            return thenExpr;
        }
        return LeastUpperBoundLogic.of(typeSolver).lub(new HashSet<>(Arrays.asList(thenExpr, elseExpr)));
    }
}
