/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2024 The JavaParser Team.
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
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.TypePatternExpr;
import com.github.javaparser.ast.stmt.WhileStmt;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.javaparsermodel.NormalCompletionVisitor;
import com.github.javaparser.symbolsolver.javaparsermodel.PatternVariableResult;
import com.github.javaparser.symbolsolver.javaparsermodel.PatternVariableVisitor;
import java.util.LinkedList;
import java.util.List;

public class WhileStatementContext extends StatementContext<WhileStmt> {

    public WhileStatementContext(WhileStmt wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    /**
     *  The following rules apply to a statement while (e) S:
     *  - A pattern variable introduced by e when true is definitely matched at S.
     *
     *  https://docs.oracle.com/javase/specs/jls/se22/html/jls-6.html#jls-6.3.2.3
     */
    @Override
    public List<TypePatternExpr> typePatternExprsExposedToChild(Node child) {
        List<TypePatternExpr> results = new LinkedList<>();

        boolean givenNodeIsWithinBody = wrappedNode.getBody().containsWithinRange(child);
        if (givenNodeIsWithinBody) {
            PatternVariableVisitor variableVisitor = new PatternVariableVisitor();
            Expression condition = wrappedNode.getCondition();
            PatternVariableResult patternsInScope = condition.accept(variableVisitor, null);

            results.addAll(patternsInScope.getVariablesIntroducedIfTrue());
        }

        return results;
    }

    /**
     * The following rules apply to a statement while (e) S:
     * - A pattern variable is introduced by while (e) S iff
     *   (i) it is introduced by e when false and
     *   (ii) S does not contain a reachable break statement for which the while statement is the break target
     *
     * https://docs.oracle.com/javase/specs/jls/se21/html/jls-6.html#jls-6.3.2.3
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
