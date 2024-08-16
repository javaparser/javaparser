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

import static com.github.javaparser.resolution.Navigator.demandParentNode;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.nodeTypes.NodeWithStatements;
import com.github.javaparser.ast.stmt.ForStmt;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.NormalCompletionVisitor;
import com.github.javaparser.symbolsolver.javaparsermodel.PatternVariableResult;
import com.github.javaparser.symbolsolver.javaparsermodel.PatternVariableVisitor;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserSymbolDeclaration;
import java.util.LinkedList;
import java.util.List;
import java.util.Optional;

public class ForStatementContext extends StatementContext<ForStmt> {

    public ForStatementContext(ForStmt wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    /**
     * The following rules apply to a basic for statement:
     * - A pattern variable introduced by the condition expression when true is definitely matched at both the
     *   incrementation part and the contained statement.
     *
     * https://docs.oracle.com/javase/specs/jls/se22/html/jls-6.html#jls-6.3.2.5
     */
    @Override
    public List<TypePatternExpr> typePatternExprsExposedToChild(Node child) {
        List<TypePatternExpr> results = new LinkedList<>();

        boolean givenNodeIsWithinUpdate =
                wrappedNode.getUpdate().stream().anyMatch(expr -> expr.containsWithinRange(child));
        boolean givenNodeIsWithinBody = wrappedNode.getBody().containsWithinRange(child);
        if ((givenNodeIsWithinUpdate || givenNodeIsWithinBody)
                && wrappedNode.getCompare().isPresent()) {
            Expression condition = wrappedNode.getCompare().get();
            PatternVariableVisitor variableVisitor = PatternVariableVisitor.getInstance();
            PatternVariableResult patternsInScope = condition.accept(variableVisitor, null);

            results.addAll(patternsInScope.getVariablesIntroducedIfTrue());
        }

        return results;
    }

    /**
     * The following rules apply to a basic for statement:
     * - A pattern variable is introduced by a basic for statement iff
     *   (i) it is introduced by the condition expression when false and
     *   (ii) the contained statement, S, does not contain a reachable break for which the basic for statement is the
     *        break target.
     *
     * https://docs.oracle.com/javase/specs/jls/se21/html/jls-6.html#jls-6.3.2.5
     */
    @Override
    public List<TypePatternExpr> getIntroducedTypePatterns() {
        List<TypePatternExpr> results = new LinkedList<>();

        Optional<Expression> maybeCompare = wrappedNode.getCompare();

        if (maybeCompare.isPresent() && !NormalCompletionVisitor.containsCorrespondingBreak(wrappedNode)) {
            PatternVariableVisitor variableVisitor = PatternVariableVisitor.getInstance();
            PatternVariableResult patternsInScope = maybeCompare.get().accept(variableVisitor, null);

            results.addAll(patternsInScope.getVariablesIntroducedIfFalse());
        }

        return results;
    }

    @Override
    public SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name) {
        for (Expression expression : wrappedNode.getInitialization()) {
            if (expression instanceof VariableDeclarationExpr) {
                VariableDeclarationExpr variableDeclarationExpr = (VariableDeclarationExpr) expression;
                for (VariableDeclarator variableDeclarator : variableDeclarationExpr.getVariables()) {
                    if (variableDeclarator.getName().getId().equals(name)) {
                        return SymbolReference.solved(
                                JavaParserSymbolDeclaration.localVar(variableDeclarator, typeSolver));
                    }
                }
            } else if (!(expression instanceof AssignExpr
                    || expression instanceof MethodCallExpr
                    || expression instanceof UnaryExpr)) {
                throw new UnsupportedOperationException(expression.getClass().getCanonicalName());
            }
        }

        if (demandParentNode(wrappedNode) instanceof NodeWithStatements) {
            return StatementContext.solveInBlock(name, typeSolver, wrappedNode);
        }
        return solveSymbolInParentContext(name);
    }

    @Override
    public SymbolReference<ResolvedMethodDeclaration> solveMethod(
            String name, List<ResolvedType> argumentsTypes, boolean staticOnly) {
        // TODO: Document why staticOnly is forced to be false.
        return solveMethodInParentContext(name, argumentsTypes, false);
    }

    @Override
    public List<VariableDeclarator> localVariablesExposedToChild(Node child) {
        List<VariableDeclarator> res = new LinkedList<>();
        for (Expression expression : wrappedNode.getInitialization()) {
            if (expression instanceof VariableDeclarationExpr) {
                VariableDeclarationExpr variableDeclarationExpr = (VariableDeclarationExpr) expression;
                res.addAll(variableDeclarationExpr.getVariables());
            }
        }
        return res;
    }
}
