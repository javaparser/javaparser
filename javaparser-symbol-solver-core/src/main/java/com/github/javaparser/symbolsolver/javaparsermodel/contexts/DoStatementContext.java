/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2026 The JavaParser Team.
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

import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.TypePatternExpr;
import com.github.javaparser.ast.stmt.DoStmt;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.javaparsermodel.NormalCompletionVisitor;
import com.github.javaparser.symbolsolver.javaparsermodel.PatternVariableResult;
import com.github.javaparser.symbolsolver.javaparsermodel.PatternVariableVisitor;
import java.util.LinkedList;
import java.util.List;

public class DoStatementContext extends StatementContext<DoStmt> {

    public DoStatementContext(DoStmt wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    /**
     * The following rule applies to a statement do S while (e):
     * - A pattern variable is introduced by do S while (e) iff
     *   (i) it is introduced by e when false and
     *   (ii) S does not contain a reachable break statement for which the do statement is the break target.
     *
     * https://docs.oracle.com/javase/specs/jls/se21/html/jls-6.html#jls-6.3.2.4
     */
    @Override
    public List<TypePatternExpr> getIntroducedTypePatterns() {
        List<TypePatternExpr> results = new LinkedList<>();

        if (!NormalCompletionVisitor.containsCorrespondingBreak(wrappedNode)) {
            Expression condition = wrappedNode.getCondition();

            PatternVariableVisitor variableVisitor = new PatternVariableVisitor();
            PatternVariableResult patternsInScope = condition.accept(variableVisitor, null);

            results.addAll(patternsInScope.getVariablesIntroducedIfFalse());
        }

        return results;
    }
}
