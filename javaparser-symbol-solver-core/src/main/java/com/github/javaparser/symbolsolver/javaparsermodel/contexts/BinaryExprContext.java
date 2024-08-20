/*
 * Copyright (C) 2013-2024 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.BinaryExpr;
import com.github.javaparser.ast.expr.TypePatternExpr;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.javaparsermodel.PatternVariableResult;
import com.github.javaparser.symbolsolver.javaparsermodel.PatternVariableVisitor;
import java.util.*;

public class BinaryExprContext extends ExpressionContext<BinaryExpr> {

    public BinaryExprContext(BinaryExpr wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    public List<TypePatternExpr> typePatternExprsExposedToChild(Node child) {
        if (wrappedNode.getOperator().equals(BinaryExpr.Operator.AND)) {
            return typePatternExprsExposedToChildByAnd(child);
        }
        if (wrappedNode.getOperator().equals(BinaryExpr.Operator.OR)) {
            return typePatternExprsExposedToChildByOr(child);
        }
        return Collections.emptyList();
    }

    /**
     * The following rules apply to a conditional-and expression a && b:
     * - A pattern variable introduced by a when true is definitely matched at b.
     *
     * https://docs.oracle.com/javase/specs/jls/se21/html/jls-6.html#jls-6.3.1.1
     */
    private List<TypePatternExpr> typePatternExprsExposedToChildByAnd(Node child) {
        if (!wrappedNode.getOperator().equals(BinaryExpr.Operator.AND)) {
            throw new IllegalStateException(
                    "Attempting to find patterns exposed by &&-expression, but wrapped operator is a "
                            + wrappedNode.getOperator().asString());
        }

        List<TypePatternExpr> results = new LinkedList<>();

        if (wrappedNode.getRight().containsWithinRange(child)) {
            PatternVariableVisitor variableVisitor = PatternVariableVisitor.getInstance();
            PatternVariableResult patternsInScope = wrappedNode.getLeft().accept(variableVisitor, null);

            results.addAll(patternsInScope.getVariablesIntroducedIfTrue());
        }

        return results;
    }

    /**
     * The following rules apply to a conditional-and expression a || b:
     * - A pattern variable introduced by a when false is definitely matched at b.
     *
     * https://docs.oracle.com/javase/specs/jls/se21/html/jls-6.html#jls-6.3.1.2
     */
    private List<TypePatternExpr> typePatternExprsExposedToChildByOr(Node child) {
        if (!wrappedNode.getOperator().equals(BinaryExpr.Operator.OR)) {
            throw new IllegalStateException(
                    "Attempting to find patterns exposed by ||-expression, but wrapped operator is a "
                            + wrappedNode.getOperator().asString());
        }

        List<TypePatternExpr> results = new LinkedList<>();

        if (wrappedNode.getRight().containsWithinRange(child)) {
            PatternVariableVisitor variableVisitor = PatternVariableVisitor.getInstance();
            PatternVariableResult patternsInScope = wrappedNode.getLeft().accept(variableVisitor, null);

            results.addAll(patternsInScope.getVariablesIntroducedIfFalse());
        }

        return results;
    }
}
